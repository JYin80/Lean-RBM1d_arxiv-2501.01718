/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Loop.Chain
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus

/-!
# Splitting loops into chains: (5.2), (5.114)–(5.118), (6.4) and Lemma 6.1

Everything here is for a **fixed deterministic Hermitian** `H` and a fixed spectral
parameter `z`; there is no probability.  All the statements are consequences of the
Cauchy–Schwarz inequality and of the structure `E_a = W⁻¹ · 1_{I_a}` of the block
projections.

* **(5.2)** `norm_gloop_le_opNorm`: with `‖G‖_op ≤ |Im z|⁻¹` (`norm_green_le`) and
  `‖E_a‖_op ≤ W⁻¹` (`norm_Eblk_le`), every loop of length `n ≥ 1` satisfies
  `|L_{σ,a}| ≤ |Im z|^{-n} W^{-n+1}`.  The operator norm is the `ℓ² → ℓ²` norm
  (`Matrix.Norms.L2Operator`, opened only in that section).
* **(5.114)–(5.115)** `gloop_append_eq_trace`, `norm_sq_gloop_le_symIdx`,
  `norm_gloop_le_of_symIdx_le`: a loop cut at two labels is `Tr(C_A E_{b'} C_B E_b)`
  for two `G`-chains, and Cauchy–Schwarz bounds it by the *symmetric* loops
  `⟨C E_{b'} C† E_b⟩` (`symIdx`) of the two chains.
* **(5.116)** `norm_gloop_symIdx_split_le`: the symmetric loop of `C₁ E_c C₂` is bounded by
  the product of the symmetric loops of `C₁` and `C₂`.
* **(5.117)** `loopMax_two_mul_add_le` (any split `l₁ + l₂`) and
  `loopMax_two_mul_add_two_le` (the paper's `l₁ = ⌊(n+1)/2⌋`):
  `max|L^{(2n+2)}| ≤ max|L^{(2l₁)}| · max|L^{(2l₂)}|`.
* **(5.118)** `loopXi_le`: `Ξ_{2n+2} ≤ Ξ_{2l₁} Ξ_{2l₂} · A` with `Ξ_m = max|L^{(m)}| A^{m-1}`.
* **(6.4)** `loopMax_odd_sq_le`: `(max|L^{(2m+1)}|)² ≤ max|L^{(2m)}| · max|L^{(2m+2)}|`.
* **Lemma 6.1** `sum_norm_inner_sq_le_trace_rpow` (real `p ≥ 1`, `A^p` by the continuous
  functional calculus) and `sum_norm_inner_sq_le_trace_pow` (natural `p ≥ 1`, matrix power):
  `∑_i |⟨v, w_i⟩|² ≤ ‖v‖² (tr A^p)^{1/p}` for the Gram matrix `A_{ij} = ⟨w_i, w_j⟩`.

The matrix-level engine is `wmass u v X = ∑_{i,j} u_i v_j |X_{ij}|²` with the two
inequalities `norm_sq_trace_mul_diagonal_le` and `wmass_mul_diagonal_mul_le`.

`loopMax L W H z n` is `max_{σ,a} |L_{σ,a}|` over all charge and label lists of length `n`
(an `iSup` over the finite type `(Fin n → Bool) × (Fin n → ZMod L)`).
-/

namespace RBM

open Matrix

section Mass

variable {n : Type*} [Fintype n]

/-- The weighted Hilbert–Schmidt mass `∑_{i,j} u_i v_j |X_{ij}|²`. -/
noncomputable def wmass (u v : n → ℝ) (X : Matrix n n ℂ) : ℝ :=
  ∑ i, ∑ j, u i * v j * ‖X i j‖ ^ 2

theorem wmass_nonneg {u v : n → ℝ} (hu : ∀ i, 0 ≤ u i) (hv : ∀ j, 0 ≤ v j)
    (X : Matrix n n ℂ) : 0 ≤ wmass u v X :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    mul_nonneg (mul_nonneg (hu i) (hv j)) (sq_nonneg _)

variable [DecidableEq n]

/-- `Tr(X D_v Y D_u) = ∑_{i,j} u_i v_j X_{ij} Y_{ji}` for diagonal `D_u`, `D_v`. -/
theorem trace_mul_diagonal_mul_mul_diagonal (u v : n → ℝ) (X Y : Matrix n n ℂ) :
    trace (X * diagonal (fun j => (v j : ℂ)) * Y * diagonal (fun i => (u i : ℂ)))
      = ∑ i, ∑ j, ((u i * v j : ℝ) : ℂ) * (X i j * Y j i) := by
  simp only [trace, diag_apply, mul_apply, diagonal_apply, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  push_cast
  ring

/-- `Tr(X D_v X† D_u) = ∑_{i,j} u_i v_j |X_{ij}|²`. -/
theorem trace_mul_diagonal_mul_conjTranspose_mul_diagonal (u v : n → ℝ) (X : Matrix n n ℂ) :
    trace (X * diagonal (fun j => (v j : ℂ)) * Xᴴ * diagonal (fun i => (u i : ℂ)))
      = (wmass u v X : ℂ) := by
  rw [trace_mul_diagonal_mul_mul_diagonal, wmass]
  push_cast
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [conjTranspose_apply, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

/-- **Weighted Cauchy–Schwarz for a trace.**
`|Tr(X D_v Y D_u)|² ≤ (∑ u_i v_j |X_{ij}|²)(∑ v_j u_i |Y_{ji}|²)`. -/
theorem norm_sq_trace_mul_diagonal_le {u v : n → ℝ} (hu : ∀ i, 0 ≤ u i) (hv : ∀ j, 0 ≤ v j)
    (X Y : Matrix n n ℂ) :
    ‖trace (X * diagonal (fun j => (v j : ℂ)) * Y * diagonal (fun i => (u i : ℂ)))‖ ^ 2
      ≤ wmass u v X * wmass v u Y := by
  rw [trace_mul_diagonal_mul_mul_diagonal]
  have h1 : ‖∑ i, ∑ j, ((u i * v j : ℝ) : ℂ) * (X i j * Y j i)‖
      ≤ ∑ p : n × n, u p.1 * v p.2 * ‖X p.1 p.2‖ * ‖Y p.2 p.1‖ := by
    rw [← Fintype.sum_prod_type']
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun p _ => ?_))
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (mul_nonneg (hu _) (hv _))]
    ring
  have h2 : (∑ p : n × n, u p.1 * v p.2 * ‖X p.1 p.2‖ * ‖Y p.2 p.1‖) ^ 2
      ≤ (∑ p : n × n, u p.1 * v p.2 * ‖X p.1 p.2‖ ^ 2)
        * ∑ p : n × n, u p.1 * v p.2 * ‖Y p.2 p.1‖ ^ 2 := by
    refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _
      (fun p _ => mul_nonneg (mul_nonneg (hu _) (hv _)) (sq_nonneg _))
      (fun p _ => mul_nonneg (mul_nonneg (hu _) (hv _)) (sq_nonneg _)) fun p _ => le_of_eq ?_
    ring
  have hX : ∑ p : n × n, u p.1 * v p.2 * ‖X p.1 p.2‖ ^ 2 = wmass u v X := by
    rw [wmass, ← Fintype.sum_prod_type']
  have hY : ∑ p : n × n, u p.1 * v p.2 * ‖Y p.2 p.1‖ ^ 2 = wmass v u Y := by
    rw [wmass, Finset.sum_comm, ← Fintype.sum_prod_type']
    refine Finset.sum_congr rfl fun p _ => ?_
    ring
  rw [hX, hY] at h2
  calc ‖∑ i, ∑ j, ((u i * v j : ℝ) : ℂ) * (X i j * Y j i)‖ ^ 2
      ≤ (∑ p : n × n, u p.1 * v p.2 * ‖X p.1 p.2‖ * ‖Y p.2 p.1‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2

/-- **Splitting a chain** (the second Cauchy–Schwarz of (5.116)).
`∑ u_i v_j |(P D_e Q)_{ij}|² ≤ (∑ u_i e_k |P_{ik}|²)(∑ e_k v_j |Q_{kj}|²)`. -/
theorem wmass_mul_diagonal_mul_le {u v e : n → ℝ} (hu : ∀ i, 0 ≤ u i) (hv : ∀ j, 0 ≤ v j)
    (he : ∀ k, 0 ≤ e k) (P Q : Matrix n n ℂ) :
    wmass u v (P * diagonal (fun k => (e k : ℂ)) * Q) ≤ wmass u e P * wmass e v Q := by
  have hentry : ∀ i j, ‖(P * diagonal (fun k => (e k : ℂ)) * Q) i j‖ ^ 2
      ≤ (∑ k, e k * ‖P i k‖ ^ 2) * ∑ k, e k * ‖Q k j‖ ^ 2 := by
    intro i j
    have h1 : ‖(P * diagonal (fun k => (e k : ℂ)) * Q) i j‖ ≤ ∑ k, e k * ‖P i k‖ * ‖Q k j‖ := by
      rw [mul_apply]
      simp only [mul_diagonal]
      refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_))
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (he k)]
      ring
    refine (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans ?_
    refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _
      (fun k _ => mul_nonneg (he k) (sq_nonneg _))
      (fun k _ => mul_nonneg (he k) (sq_nonneg _)) fun k _ => le_of_eq ?_
    ring
  calc wmass u v (P * diagonal (fun k => (e k : ℂ)) * Q)
      ≤ ∑ i, ∑ j, u i * v j * ((∑ k, e k * ‖P i k‖ ^ 2) * ∑ k, e k * ‖Q k j‖ ^ 2) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (hentry i j) (mul_nonneg (hu i) (hv j))
    _ = (∑ i, u i * ∑ k, e k * ‖P i k‖ ^ 2) * ∑ j, v j * ∑ k, e k * ‖Q k j‖ ^ 2 := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum Finset.univ (fun j => v j * ∑ k, e k * ‖Q k j‖ ^ 2)
          (u i * ∑ k, e k * ‖P i k‖ ^ 2)]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
    _ = wmass u e P * wmass e v Q := by
        congr 1
        · rw [wmass]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          ring
        · rw [wmass, Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          ring

end Mass

section Block

variable {L W : ℕ}

/-- The real weight of the block projection: `E_b = diag(bw b)`, `bw b p = W⁻¹ 1(p ∈ I_b)`. -/
noncomputable def bw (b : ZMod L) (p : ZMod L × Fin W) : ℝ := if p.1 = b then (W : ℝ)⁻¹ else 0

theorem bw_nonneg (b : ZMod L) (p : ZMod L × Fin W) : 0 ≤ bw b p := by
  unfold bw
  split_ifs <;> positivity

theorem Eblk_eq_diagonal_bw (b : ZMod L) :
    Eblk L W b = diagonal (fun p => ((bw b p : ℝ) : ℂ)) := by
  rw [Eblk]
  congr 1
  funext p
  unfold bw
  split_ifs <;> push_cast <;> rfl

variable [NeZero L]

/-- `Tr(X E_{b'} X† E_b) = ∑_{i ∈ I_b, j ∈ I_{b'}} W⁻² |X_{ij}|²`: a nonnegative real. -/
theorem trace_mul_Eblk_mul_conjTranspose_mul_Eblk (X : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ)
    (b' b : ZMod L) :
    trace (X * Eblk L W b' * Xᴴ * Eblk L W b) = (wmass (bw b) (bw b') X : ℂ) := by
  rw [Eblk_eq_diagonal_bw, Eblk_eq_diagonal_bw,
    trace_mul_diagonal_mul_conjTranspose_mul_diagonal]

theorem norm_trace_mul_Eblk_mul_conjTranspose_mul_Eblk
    (X : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (b' b : ZMod L) :
    ‖trace (X * Eblk L W b' * Xᴴ * Eblk L W b)‖ = wmass (bw b) (bw b') X := by
  rw [trace_mul_Eblk_mul_conjTranspose_mul_Eblk, Complex.norm_real,
    Real.norm_of_nonneg (wmass_nonneg (bw_nonneg b) (bw_nonneg b') X)]

/-- **The Cauchy–Schwarz step of (5.115)**, at the matrix level:
`|Tr(X E_{b'} Y E_b)|² ≤ Tr(X E_{b'} X† E_b) · Tr(Y E_b Y† E_{b'})`. -/
theorem norm_sq_trace_Eblk_le (X Y : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ)
    (b' b : ZMod L) :
    ‖trace (X * Eblk L W b' * Y * Eblk L W b)‖ ^ 2
      ≤ ‖trace (X * Eblk L W b' * Xᴴ * Eblk L W b)‖
        * ‖trace (Y * Eblk L W b * Yᴴ * Eblk L W b')‖ := by
  rw [norm_trace_mul_Eblk_mul_conjTranspose_mul_Eblk,
    norm_trace_mul_Eblk_mul_conjTranspose_mul_Eblk, Eblk_eq_diagonal_bw, Eblk_eq_diagonal_bw]
  exact norm_sq_trace_mul_diagonal_le (bw_nonneg b) (bw_nonneg b') X Y

/-- **The Cauchy–Schwarz step of (5.116)**, at the matrix level: for a chain `P E_c Q`,
`Tr((P E_c Q) E_{b'} (P E_c Q)† E_b) ≤ Tr(P E_c P† E_b) · Tr(Q E_{b'} Q† E_c)`. -/
theorem norm_trace_Eblk_split_le (P Q : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ)
    (c b' b : ZMod L) :
    ‖trace ((P * Eblk L W c * Q) * Eblk L W b' * (P * Eblk L W c * Q)ᴴ * Eblk L W b)‖
      ≤ ‖trace (P * Eblk L W c * Pᴴ * Eblk L W b)‖
        * ‖trace (Q * Eblk L W b' * Qᴴ * Eblk L W c)‖ := by
  rw [norm_trace_mul_Eblk_mul_conjTranspose_mul_Eblk,
    norm_trace_mul_Eblk_mul_conjTranspose_mul_Eblk,
    norm_trace_mul_Eblk_mul_conjTranspose_mul_Eblk, Eblk_eq_diagonal_bw]
  exact wmass_mul_diagonal_mul_le (bw_nonneg b) (bw_nonneg b') (bw_nonneg c) P Q

end Block

section Chains

variable {L W : ℕ} [NeZero L] [NeZero W]
  {H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ} {z : ℂ}

/-- Concatenating two chains through one `E_c`. -/
theorem gchain_append {σ₁ : List Bool} {a₁ : List (ZMod L)} (h : σ₁.length = a₁.length + 1)
    (σ₂ : List Bool) (c : ZMod L) (a₂ : List (ZMod L)) :
    gchain L W H z (σ₁ ++ σ₂) (a₁ ++ c :: a₂)
      = gchain L W H z σ₁ a₁ * Eblk L W c * gchain L W H z σ₂ a₂ := by
  induction σ₁ generalizing a₁ with
  | nil => simp at h
  | cons s σ ih =>
    cases a₁ with
    | nil =>
      have hσ : σ = [] := List.eq_nil_of_length_eq_zero (by simpa using h)
      subst hσ
      rfl
    | cons b a =>
      have h' : σ.length = a.length + 1 := by simpa using h
      rw [List.cons_append, List.cons_append, gchain_cons, gchain_cons, ih h']
      simp only [Matrix.mul_assoc]

/-- A loop cut at two places is the trace of two chains:
`L_{σ_A σ_B, (a_A b') (a_B b)} = Tr(C_A E_{b'} C_B E_b)`. -/
theorem gloop_append_eq_trace {σA σB : List Bool} {aA aB : List (ZMod L)}
    (hA : σA.length = aA.length + 1) (hB : σB.length = aB.length + 1) (b' b : ZMod L) :
    gloop L W H z ⟨σA ++ σB, (aA ++ [b']) ++ (aB ++ [b])⟩
      = trace (gchain L W H z σA aA * Eblk L W b' * gchain L W H z σB aB * Eblk L W b) := by
  have hA' : σA.length = (aA ++ [b']).length := by simp [hA]
  rw [gloop, gloopProd_append hA', ← gchain_mul_Eblk hA, ← gchain_mul_Eblk hB]
  simp only [Matrix.mul_assoc]

/-- The **symmetric loop** of a chain `C = C_{σ,a}`: the loop `⟨C E_{b'} C† E_b⟩` of (6.5),
of length `2 σ.length`. -/
def symIdx {L : ℕ} (σ : List Bool) (a : List (ZMod L)) (b' b : ZMod L) : LoopIdx (ZMod L) :=
  ⟨σ ++ (σ.map (!·)).reverse, (a ++ [b']) ++ (a.reverse ++ [b])⟩

omit [NeZero L] in
@[simp] theorem symIdx_σ_length (σ : List Bool) (a : List (ZMod L)) (b' b : ZMod L) :
    (symIdx σ a b' b).σ.length = 2 * σ.length := by
  simp [symIdx]; ring

omit [NeZero L] in
@[simp] theorem symIdx_a_length (σ : List Bool) (a : List (ZMod L)) (b' b : ZMod L) :
    (symIdx σ a b' b).a.length = 2 * (a.length + 1) := by
  simp [symIdx]; ring

theorem gloop_symIdx (hH : H.IsHermitian) {σ : List Bool} {a : List (ZMod L)}
    (h : σ.length = a.length + 1) (b' b : ZMod L) :
    gloop L W H z (symIdx σ a b' b)
      = trace (gchain L W H z σ a * Eblk L W b' * (gchain L W H z σ a)ᴴ * Eblk L W b) := by
  rw [gchain_conjTranspose hH h]
  exact gloop_append_eq_trace h (by simpa using h) b' b

/-- **(5.115), one loop at a time**: a loop cut into two chains `C_A`, `C_B` is bounded by
the symmetric loops of the two chains,
`|L_{σ,a}|² ≤ |⟨C_A E_{b'} C_A† E_b⟩| · |⟨C_B E_b C_B† E_{b'}⟩|`. -/
theorem norm_sq_gloop_le_symIdx (hH : H.IsHermitian) {σA σB : List Bool}
    {aA aB : List (ZMod L)} (hA : σA.length = aA.length + 1) (hB : σB.length = aB.length + 1)
    (b' b : ZMod L) :
    ‖gloop L W H z ⟨σA ++ σB, (aA ++ [b']) ++ (aB ++ [b])⟩‖ ^ 2
      ≤ ‖gloop L W H z (symIdx σA aA b' b)‖ * ‖gloop L W H z (symIdx σB aB b b')‖ := by
  rw [gloop_append_eq_trace hA hB, gloop_symIdx hH hA, gloop_symIdx hH hB]
  exact norm_sq_trace_Eblk_le _ _ b' b

/-- **(5.116), one loop at a time**: the symmetric loop of a chain `C = C₁ E_c C₂` is bounded
by the product of the symmetric loops of `C₁` and `C₂`. -/
theorem norm_gloop_symIdx_split_le (hH : H.IsHermitian) {σ₁ σ₂ : List Bool}
    {a₁ a₂ : List (ZMod L)} (h₁ : σ₁.length = a₁.length + 1) (h₂ : σ₂.length = a₂.length + 1)
    (c b' b : ZMod L) :
    ‖gloop L W H z (symIdx (σ₁ ++ σ₂) (a₁ ++ c :: a₂) b' b)‖
      ≤ ‖gloop L W H z (symIdx σ₁ a₁ c b)‖ * ‖gloop L W H z (symIdx σ₂ a₂ b' c)‖ := by
  have h : (σ₁ ++ σ₂).length = (a₁ ++ c :: a₂).length + 1 := by simp [h₁, h₂]; ring
  rw [gloop_symIdx hH h, gloop_symIdx hH h₁, gloop_symIdx hH h₂, gchain_append h₁]
  exact norm_trace_Eblk_split_le _ _ c b' b

end Chains

section Decompose

variable {α β : Type*}

/-- Cutting a loop's index data into two chains closed by one label each. -/
theorem exists_split_loopIdx {k₁ k₂ : ℕ} (h₁ : 1 ≤ k₁) (h₂ : 1 ≤ k₂) {σ : List α} {a : List β}
    (hσ : σ.length = k₁ + k₂) (ha : a.length = k₁ + k₂) :
    ∃ (σA σB : List α) (aA aB : List β) (b' b : β),
      σ = σA ++ σB ∧ a = (aA ++ [b']) ++ (aB ++ [b]) ∧
      σA.length = k₁ ∧ aA.length + 1 = k₁ ∧ σB.length = k₂ ∧ aB.length + 1 = k₂ := by
  have hA : (a.take k₁).length = k₁ := by simp [ha]
  have hB : (a.drop k₁).length = k₂ := by simp [ha]
  rcases List.eq_nil_or_concat' (a.take k₁) with h0 | ⟨aA, b', hAeq⟩
  · rw [h0] at hA; simp at hA; omega
  rcases List.eq_nil_or_concat' (a.drop k₁) with h0 | ⟨aB, b, hBeq⟩
  · rw [h0] at hB; simp at hB; omega
  refine ⟨σ.take k₁, σ.drop k₁, aA, aB, b', b, (List.take_append_drop _ _).symm, ?_, ?_, ?_,
    ?_, ?_⟩
  · rw [← hAeq, ← hBeq, List.take_append_drop]
  · simp [hσ]
  · rw [hAeq] at hA; simpa using hA
  · simp [hσ]
  · rw [hBeq] at hB; simpa using hB

/-- Cutting a chain's index data at one of its labels. -/
theorem exists_split_chainIdx {l₁ l₂ : ℕ} (h₁ : 1 ≤ l₁) (h₂ : 1 ≤ l₂) {σ : List α} {a : List β}
    (hσ : σ.length = l₁ + l₂) (ha : a.length + 1 = l₁ + l₂) :
    ∃ (σ₁ σ₂ : List α) (a₁ a₂ : List β) (c : β),
      σ = σ₁ ++ σ₂ ∧ a = a₁ ++ c :: a₂ ∧
      σ₁.length = l₁ ∧ a₁.length + 1 = l₁ ∧ σ₂.length = l₂ ∧ a₂.length + 1 = l₂ := by
  have hB : (a.drop (l₁ - 1)).length = l₂ := by simp [List.length_drop]; omega
  rcases hd : a.drop (l₁ - 1) with _ | ⟨c, a₂⟩
  · rw [hd] at hB; simp at hB; omega
  refine ⟨σ.take l₁, σ.drop l₁, a.take (l₁ - 1), a₂, c, (List.take_append_drop _ _).symm, ?_,
    ?_, ?_, ?_, ?_⟩
  · rw [← hd, List.take_append_drop]
  · simp [hσ]
  · simp; omega
  · simp [hσ]
  · rw [hd] at hB; simpa using hB

end Decompose

section Max

variable {L W : ℕ} [NeZero L] [NeZero W]

variable (L W) in
/-- `max_{σ,a} |L_{σ,a}|` over all loops of length `n`, the quantity bounded in (5.117) and
(6.4). -/
noncomputable def loopMax (H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (z : ℂ) (n : ℕ) : ℝ :=
  ⨆ x : (Fin n → Bool) × (Fin n → ZMod L), ‖gloop L W H z ⟨List.ofFn x.1, List.ofFn x.2⟩‖

variable {H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ} {z : ℂ}

omit [NeZero W] in
theorem norm_gloop_le_loopMax {n : ℕ} (I : LoopIdx (ZMod L)) (hσ : I.σ.length = n)
    (ha : I.a.length = n) : ‖gloop L W H z I‖ ≤ loopMax L W H z n := by
  obtain ⟨σ, a⟩ := I
  simp only at hσ ha
  subst hσ
  have hσ' : List.ofFn (fun i : Fin σ.length => σ.get i) = σ := List.ofFn_get σ
  have ha' : List.ofFn (fun i : Fin σ.length => a.get (Fin.cast ha.symm i)) = a := by
    apply List.ext_get <;> simp [ha]
  refine le_of_eq_of_le ?_ (le_ciSup (Set.finite_range _).bddAbove
    ((fun i => σ.get i, fun i => a.get (Fin.cast ha.symm i)) :
      (Fin σ.length → Bool) × (Fin σ.length → ZMod L)))
  simp only [hσ', ha']

omit [NeZero W] in
theorem loopMax_le {n : ℕ} {M : ℝ}
    (hM : ∀ I : LoopIdx (ZMod L), I.σ.length = n → I.a.length = n → ‖gloop L W H z I‖ ≤ M) :
    loopMax L W H z n ≤ M :=
  ciSup_le fun x => hM _ (by simp) (by simp)

omit [NeZero W] in
theorem loopMax_nonneg (n : ℕ) : 0 ≤ loopMax L W H z n :=
  Real.iSup_nonneg fun _ => norm_nonneg _

omit [NeZero W] in
/-- The symmetric loop of a chain with `k` `G`'s is a loop of length `2k`. -/
theorem norm_gloop_symIdx_le_loopMax {σ : List Bool} {a : List (ZMod L)}
    (h : σ.length = a.length + 1) (b' b : ZMod L) :
    ‖gloop L W H z (symIdx σ a b' b)‖ ≤ loopMax L W H z (2 * σ.length) :=
  norm_gloop_le_loopMax _ (by simp) (by simp [h])

/-- **(5.116)**: the symmetric loop of an `(l₁ + l₂)`-chain is bounded by
`max|L^{(2l₁)}| · max|L^{(2l₂)}|`. -/
theorem norm_gloop_symIdx_le_loopMax_mul (hH : H.IsHermitian) {l₁ l₂ : ℕ} (h₁ : 1 ≤ l₁)
    (h₂ : 1 ≤ l₂) {σ : List Bool} {a : List (ZMod L)} (hσ : σ.length = l₁ + l₂)
    (ha : a.length + 1 = l₁ + l₂) (b' b : ZMod L) :
    ‖gloop L W H z (symIdx σ a b' b)‖
      ≤ loopMax L W H z (2 * l₁) * loopMax L W H z (2 * l₂) := by
  obtain ⟨σ₁, σ₂, a₁, a₂, c, rfl, rfl, hσ₁, ha₁, hσ₂, ha₂⟩ :=
    exists_split_chainIdx h₁ h₂ hσ ha
  refine (norm_gloop_symIdx_split_le hH (by omega) (by omega) c b' b).trans ?_
  refine mul_le_mul ?_ ?_ (norm_nonneg _) (loopMax_nonneg _)
  · rw [← hσ₁]; exact norm_gloop_symIdx_le_loopMax (by omega) c b
  · rw [← hσ₂]; exact norm_gloop_symIdx_le_loopMax (by omega) b' c

/-- **(5.115)**: every loop of length `2k` is bounded by the largest *symmetric* loop
`⟨C E_{b'} C† E_b⟩` built from a `k`-chain `C`. -/
theorem norm_gloop_le_of_symIdx_le (hH : H.IsHermitian) {k : ℕ} (hk : 1 ≤ k) {M : ℝ}
    (hM : ∀ (σ : List Bool) (a : List (ZMod L)), σ.length = k → a.length + 1 = k →
      ∀ b' b, ‖gloop L W H z (symIdx σ a b' b)‖ ≤ M)
    (I : LoopIdx (ZMod L)) (hσ : I.σ.length = 2 * k) (ha : I.a.length = 2 * k) :
    ‖gloop L W H z I‖ ≤ M := by
  obtain ⟨σ, a⟩ := I
  simp only at hσ ha
  obtain ⟨σA, σB, aA, aB, b', b, rfl, rfl, hσA, haA, hσB, haB⟩ :=
    exists_split_loopIdx hk hk (by rw [hσ]; ring) (by rw [ha]; ring)
  have h := norm_sq_gloop_le_symIdx (z := z) hH (by omega : σA.length = aA.length + 1)
    (by omega : σB.length = aB.length + 1) b' b
  have h1 := hM σA aA hσA haA b' b
  have h2 := hM σB aB hσB haB b b'
  have hM0 : 0 ≤ M := (norm_nonneg _).trans h1
  have hprod := mul_le_mul h1 h2 (norm_nonneg _) hM0
  nlinarith [norm_nonneg (gloop L W H z ⟨σA ++ σB, aA ++ [b'] ++ (aB ++ [b])⟩)]

/-- **(5.117), general split**: for `l₁, l₂ ≥ 1`,
`max|L^{(2(l₁+l₂))}| ≤ max|L^{(2l₁)}| · max|L^{(2l₂)}|`. -/
theorem loopMax_two_mul_add_le (hH : H.IsHermitian) {l₁ l₂ : ℕ} (h₁ : 1 ≤ l₁) (h₂ : 1 ≤ l₂) :
    loopMax L W H z (2 * (l₁ + l₂)) ≤ loopMax L W H z (2 * l₁) * loopMax L W H z (2 * l₂) :=
  loopMax_le fun I hσ ha => norm_gloop_le_of_symIdx_le hH (by omega)
    (fun _ _ hσ' ha' b' b => norm_gloop_symIdx_le_loopMax_mul hH h₁ h₂ hσ' ha' b' b) I hσ ha

/-- **(5.117)** as stated in the paper: with `l₁ = ⌊(n+1)/2⌋`, `l₂ = n + 1 - l₁`,
`max|L^{(2n+2)}| ≤ max|L^{(2l₁)}| · max|L^{(2l₂)}|`. -/
theorem loopMax_two_mul_add_two_le (hH : H.IsHermitian) {n : ℕ} (hn : 1 ≤ n) :
    loopMax L W H z (2 * n + 2)
      ≤ loopMax L W H z (2 * ((n + 1) / 2)) * loopMax L W H z (2 * (n + 1 - (n + 1) / 2)) := by
  have h := loopMax_two_mul_add_le (z := z) hH (l₁ := (n + 1) / 2) (l₂ := n + 1 - (n + 1) / 2)
    (by omega) (by omega)
  rwa [show 2 * ((n + 1) / 2 + (n + 1 - (n + 1) / 2)) = 2 * n + 2 by omega] at h

/-- **(6.4)**: odd loops are controlled by the neighbouring even ones,
`(max|L^{(2m+1)}|)² ≤ max|L^{(2m)}| · max|L^{(2m+2)}|`. -/
theorem loopMax_odd_sq_le (hH : H.IsHermitian) {m : ℕ} (hm : 1 ≤ m) :
    loopMax L W H z (2 * m + 1) ^ 2 ≤ loopMax L W H z (2 * m) * loopMax L W H z (2 * m + 2) := by
  have hbound : ∀ I : LoopIdx (ZMod L), I.σ.length = 2 * m + 1 → I.a.length = 2 * m + 1 →
      ‖gloop L W H z I‖ ≤ Real.sqrt (loopMax L W H z (2 * m) * loopMax L W H z (2 * m + 2)) := by
    intro I hσ ha
    obtain ⟨σ, a⟩ := I
    simp only at hσ ha
    obtain ⟨σA, σB, aA, aB, b', b, rfl, rfl, hσA, haA, hσB, haB⟩ :=
      exists_split_loopIdx (k₁ := m + 1) (k₂ := m) (by omega) hm (by rw [hσ]; ring)
        (by rw [ha]; ring)
    have h := norm_sq_gloop_le_symIdx (z := z) hH (by omega : σA.length = aA.length + 1)
      (by omega : σB.length = aB.length + 1) b' b
    have h1 : ‖gloop L W H z (symIdx σA aA b' b)‖ ≤ loopMax L W H z (2 * m + 2) := by
      have := norm_gloop_symIdx_le_loopMax (H := H) (z := z) (by omega : σA.length = aA.length + 1)
        b' b
      rwa [hσA, show 2 * (m + 1) = 2 * m + 2 by ring] at this
    have h2 : ‖gloop L W H z (symIdx σB aB b b')‖ ≤ loopMax L W H z (2 * m) := by
      have := norm_gloop_symIdx_le_loopMax (H := H) (z := z) (by omega : σB.length = aB.length + 1)
        b b'
      rwa [hσB] at this
    apply Real.le_sqrt_of_sq_le
    calc _ ≤ _ := h
      _ ≤ loopMax L W H z (2 * m + 2) * loopMax L W H z (2 * m) :=
          mul_le_mul h1 h2 (norm_nonneg _) (loopMax_nonneg _)
      _ = _ := mul_comm _ _
  have hle := loopMax_le hbound
  calc loopMax L W H z (2 * m + 1) ^ 2
      ≤ Real.sqrt (loopMax L W H z (2 * m) * loopMax L W H z (2 * m + 2)) ^ 2 :=
        pow_le_pow_left₀ (loopMax_nonneg _) hle 2
    _ = _ := Real.sq_sqrt (mul_nonneg (loopMax_nonneg _) (loopMax_nonneg _))

variable (L W) in
/-- `Ξ^{(L)}_{m} = max_{σ,a} |L_{σ,a}| · A^{m-1}` of (2.82)/(5.76), with the scale
`A = Wℓ_uη_u` kept as a parameter. -/
noncomputable def loopXi (H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (z : ℂ) (A : ℝ)
    (m : ℕ) : ℝ :=
  loopMax L W H z m * A ^ (m - 1)

/-- **(5.118)**: `Ξ^{(L)}_{2n+2} ≤ Ξ^{(L)}_{2l₁} · Ξ^{(L)}_{2l₂} · A` for any split
`l₁ + l₂ = n + 1`, `l₁, l₂ ≥ 1`, and any scale `A ≥ 0`. -/
theorem loopXi_le (hH : H.IsHermitian) {A : ℝ} (hA : 0 ≤ A) {n l₁ l₂ : ℕ} (h₁ : 1 ≤ l₁)
    (h₂ : 1 ≤ l₂) (hl : l₁ + l₂ = n + 1) :
    loopXi L W H z A (2 * n + 2)
      ≤ loopXi L W H z A (2 * l₁) * loopXi L W H z A (2 * l₂) * A := by
  have h := loopMax_two_mul_add_le (z := z) hH h₁ h₂
  rw [hl, show 2 * (n + 1) = 2 * n + 2 by ring] at h
  have hpow : A ^ (2 * n + 2 - 1) = A ^ (2 * l₁ - 1) * A ^ (2 * l₂ - 1) * A := by
    rw [← pow_add, ← pow_succ]
    congr 1
    omega
  unfold loopXi
  rw [hpow]
  have hA' : 0 ≤ A ^ (2 * l₁ - 1) * A ^ (2 * l₂ - 1) * A := by positivity
  calc loopMax L W H z (2 * n + 2) * (A ^ (2 * l₁ - 1) * A ^ (2 * l₂ - 1) * A)
      ≤ loopMax L W H z (2 * l₁) * loopMax L W H z (2 * l₂)
          * (A ^ (2 * l₁ - 1) * A ^ (2 * l₂ - 1) * A) :=
        mul_le_mul_of_nonneg_right h hA'
    _ = _ := by ring

end Max

section OpNorm

open scoped Matrix.Norms.L2Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- An entry is bounded by the `ℓ² → ℓ²` operator norm. -/
theorem norm_apply_le_l2_opNorm (M : Matrix n n ℂ) (p q : n) : ‖M p q‖ ≤ ‖M‖ := by
  have h := l2_opNorm_mulVec M (EuclideanSpace.single q 1)
  rw [PiLp.norm_single, norm_one, mul_one] at h
  refine le_trans ?_ h
  refine le_of_eq_of_le ?_ (PiLp.norm_apply_le _ p)
  simp

/-- `‖(H - z)⁻¹‖_op ≤ |Im z|⁻¹` for Hermitian `H`: the input `‖G_t‖_op = 1/η_t` of (5.2). -/
theorem norm_green_le [Nonempty n] {H : Matrix n n ℂ} (hH : H.IsHermitian) {z : ℂ}
    (hz : z.im ≠ 0) : ‖green H z‖ ≤ |z.im|⁻¹ := by
  have hz' : ∀ l, (hH.eigenvalues l : ℂ) ≠ z := by
    intro l h
    have := congrArg Complex.im h
    simp at this
    exact hz this.symm
  rw [green_eq_spectral hH hz']
  have hU : ‖(hH.eigenvectorUnitary : Matrix n n ℂ)‖ = 1 := CStarRing.norm_coe_unitary _
  have hU' : ‖star (hH.eigenvectorUnitary : Matrix n n ℂ)‖ = 1 := by
    rw [star_eq_conjTranspose, l2_opNorm_conjTranspose, hU]
  refine (norm_mul_le _ _).trans ?_
  rw [hU', mul_one]
  refine (norm_mul_le _ _).trans ?_
  rw [hU, one_mul, l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun l => ?_
  rw [norm_inv]
  refine inv_anti₀ (abs_pos.mpr hz) ?_
  calc |z.im| = |((hH.eigenvalues l : ℂ) - z).im| := by simp
    _ ≤ ‖(hH.eigenvalues l : ℂ) - z‖ := Complex.abs_im_le_norm _

theorem norm_Gsig_le [Nonempty n] {H : Matrix n n ℂ} (hH : H.IsHermitian) {z : ℂ}
    (hz : z.im ≠ 0) (s : Bool) : ‖Gsig H z s‖ ≤ |z.im|⁻¹ := by
  cases s
  · have hz' : ((starRingEnd ℂ) z).im ≠ 0 := by simpa using hz
    simpa using norm_green_le hH hz'
  · exact norm_green_le hH hz

variable {L W : ℕ} [NeZero L] [NeZero W]

omit [NeZero W] in
/-- `‖E_a‖_op ≤ W⁻¹`, the second input of (5.2). -/
theorem norm_Eblk_le (b : ZMod L) : ‖Eblk L W b‖ ≤ (W : ℝ)⁻¹ := by
  rw [Eblk_eq_diagonal_bw, l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun p => ?_
  rw [Complex.norm_real, Real.norm_of_nonneg (bw_nonneg b p)]
  unfold bw
  split_ifs
  · exact le_rfl
  · positivity

theorem sum_bw (b : ZMod L) : ∑ p : ZMod L × Fin W, bw b p = 1 := by
  rw [Fintype.sum_prod_type]
  simp only [bw]
  rw [Finset.sum_eq_single b (fun x _ hx => by simp [hx]) (by simp)]
  simp only [ite_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact mul_inv_cancel₀ (by exact_mod_cast NeZero.ne W)

/-- `|⟨M E_b⟩| ≤ ‖M‖_op`: the trace against one `E_b` costs nothing. -/
theorem norm_trace_mul_Eblk_le (M : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (b : ZMod L) :
    ‖trace (M * Eblk L W b)‖ ≤ ‖M‖ := by
  rw [Eblk_eq_diagonal_bw, trace]
  simp only [diag_apply, mul_diagonal]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ p, ‖M p p * ((bw b p : ℝ) : ℂ)‖ ≤ ∑ p, ‖M‖ * bw b p := by
        refine Finset.sum_le_sum fun p _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (bw_nonneg b p)]
        exact mul_le_mul_of_nonneg_right (norm_apply_le_l2_opNorm M p p) (bw_nonneg b p)
    _ = ‖M‖ := by rw [← Finset.mul_sum, sum_bw, mul_one]

variable {H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ} {z : ℂ}

/-- `‖C_{σ,a}‖_op ≤ |Im z|^{-|σ|} W^{-|a|}`. -/
theorem norm_gchain_le (hH : H.IsHermitian) (hz : z.im ≠ 0) {σ : List Bool}
    {a : List (ZMod L)} (h : σ.length = a.length + 1) :
    ‖gchain L W H z σ a‖ ≤ |z.im|⁻¹ ^ σ.length * (W : ℝ)⁻¹ ^ a.length := by
  induction σ generalizing a with
  | nil => simp at h
  | cons s σ ih =>
    cases a with
    | nil =>
      have hσ : σ = [] := List.eq_nil_of_length_eq_zero (by simpa using h)
      subst hσ
      simpa using norm_Gsig_le hH hz s
    | cons b a =>
      have h' : σ.length = a.length + 1 := by simpa using h
      rw [gchain_cons, List.length_cons, List.length_cons, pow_succ', pow_succ']
      refine (norm_mul_le _ _).trans ?_
      refine (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)).trans ?_
      have hG := norm_Gsig_le hH hz s
      have hE := norm_Eblk_le (W := W) b
      have hC := ih h'
      calc ‖Gsig H z s‖ * ‖Eblk L W b‖ * ‖gchain L W H z σ a‖
          ≤ |z.im|⁻¹ * (W : ℝ)⁻¹ * (|z.im|⁻¹ ^ σ.length * (W : ℝ)⁻¹ ^ a.length) := by
            gcongr
        _ = _ := by ring

/-- **(5.2)**: `|L_{σ,a}| ≤ |Im z|^{-n} W^{-n+1}` for every loop of length `n ≥ 1`.
With `‖G‖_op = 1/η = O(1)` this is the paper's `L_{t,σ,a} = O(W^{-n+1})`. -/
theorem norm_gloop_le_opNorm (hH : H.IsHermitian) (hz : z.im ≠ 0) (I : LoopIdx (ZMod L))
    (hwf : I.σ.length = I.a.length) (hn : 1 ≤ I.a.length) :
    ‖gloop L W H z I‖ ≤ |z.im|⁻¹ ^ I.a.length * (W : ℝ)⁻¹ ^ (I.a.length - 1) := by
  obtain ⟨σ, a⟩ := I
  simp only at hwf hn ⊢
  rcases List.eq_nil_or_concat' a with rfl | ⟨a', b, rfl⟩
  · simp at hn
  have h : σ.length = a'.length + 1 := by simpa using hwf
  rw [← trace_gchain_mul_Eblk h b]
  refine (norm_trace_mul_Eblk_le _ b).trans ?_
  refine (norm_gchain_le hH hz h).trans (le_of_eq ?_)
  simp [h]

/-- **(5.2)**, `O(·)` form: if `|Im z| ≥ η > 0` then `|L_{σ,a}| ≤ η^{-n} W^{-n+1}`. -/
theorem norm_gloop_le_of_le_abs_im (hH : H.IsHermitian) {η : ℝ} (hη : 0 < η)
    (hz : η ≤ |z.im|) (I : LoopIdx (ZMod L)) (hwf : I.σ.length = I.a.length)
    (hn : 1 ≤ I.a.length) :
    ‖gloop L W H z I‖ ≤ η⁻¹ ^ I.a.length * (W : ℝ)⁻¹ ^ (I.a.length - 1) := by
  have hz0 : z.im ≠ 0 := abs_pos.mp (hη.trans_le hz)
  refine (norm_gloop_le_opNorm hH hz0 I hwf hn).trans ?_
  gcongr

end OpNorm

section Gram

open scoped ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A Hermitian quadratic form is bounded by any upper bound of the spectrum:
`Re(c* A c) ≤ M ∑ |c_i|²` if every eigenvalue of `A` is `≤ M`. -/
theorem re_dotProduct_mulVec_le {A : Matrix ι ι ℂ} (hA : A.IsHermitian) {M : ℝ}
    (hM : ∀ k, hA.eigenvalues k ≤ M) (c : ι → ℂ) :
    (star c ⬝ᵥ A *ᵥ c).re ≤ M * ∑ i, ‖c i‖ ^ 2 := by
  set U : Matrix ι ι ℂ := (hA.eigenvectorUnitary : Matrix ι ι ℂ) with hU
  have hspec : A = U * diagonal (RCLike.ofReal ∘ hA.eigenvalues) * star U := by
    conv_lhs => rw [hA.spectral_theorem]
    rfl
  have hB : ((M : ℂ) • (1 : Matrix ι ι ℂ) - A).PosSemidef := by
    have hdiag : (diagonal (fun k => ((M - hA.eigenvalues k : ℝ) : ℂ))).PosSemidef :=
      posSemidef_diagonal_iff.mpr fun k => by
        exact_mod_cast (Complex.zero_le_real.mpr (sub_nonneg.mpr (hM k)))
    have h := hdiag.mul_mul_conjTranspose_same U
    have e1 : diagonal (fun k => ((M - hA.eigenvalues k : ℝ) : ℂ))
        = (M : ℂ) • (1 : Matrix ι ι ℂ) - diagonal (RCLike.ofReal ∘ hA.eigenvalues) := by
      ext i j
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    have hUU : U * star U = 1 := Unitary.coe_mul_star_self _
    rw [e1, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
      ← star_eq_conjTranspose, hUU, ← hspec] at h
    exact h
  have h0 := hB.re_dotProduct_nonneg c
  have hcc : (star c ⬝ᵥ c) = ((∑ i, ‖c i‖ ^ 2 : ℝ) : ℂ) := by
    simp only [dotProduct, Pi.star_apply, RCLike.star_def]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.conj_mul']
  rw [sub_mulVec, dotProduct_sub, smul_mulVec, one_mulVec, dotProduct_smul, hcc,
    smul_eq_mul, map_sub] at h0
  simp only [RCLike.re_to_complex] at h0
  rw [← Complex.ofReal_mul, Complex.ofReal_re] at h0
  linarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **Lemma 6.1, spectral form**: if `M ≥ 0` bounds the spectrum of the Gram matrix
`A_{ij} = ⟨w_i, w_j⟩`, then `∑_i |⟨v, w_i⟩|² ≤ ‖v‖² M`. -/
theorem sum_norm_inner_sq_le_of_eigenvalues_le (v : E) (w : ι → E) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ k, (posSemidef_gram ℂ w).isHermitian.eigenvalues k ≤ M) :
    ∑ i, ‖inner ℂ v (w i)‖ ^ 2 ≤ ‖v‖ ^ 2 * M := by
  set c : ι → ℂ := fun i => inner ℂ (w i) v with hc
  set S : ℝ := ∑ i, ‖inner ℂ v (w i)‖ ^ 2 with hS
  have hSc : S = ∑ i, ‖c i‖ ^ 2 := by
    rw [hS]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [norm_inner_symm]
  set u : E := ∑ i, c i • w i with hu
  have huv : inner ℂ u v = (S : ℂ) := by
    rw [hu, sum_inner, hSc]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_smul_left, Complex.conj_mul']
  have huu : inner ℂ u u = star c ⬝ᵥ (gram ℂ w *ᵥ c) := by
    rw [hu, sum_inner]
    simp only [dotProduct, mulVec, Pi.star_apply, RCLike.star_def, gram_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_smul_left, inner_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inner_smul_right]
    ring
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
  have h1 : S ≤ ‖u‖ * ‖v‖ := by
    have := re_inner_le_norm (𝕜 := ℂ) u v
    rw [huv] at this
    simpa using this
  have h2 : ‖u‖ ^ 2 ≤ M * S := by
    have h := re_dotProduct_mulVec_le (posSemidef_gram ℂ w).isHermitian hM c
    rw [← huu, ← hSc, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow] at h
    have e : (((‖u‖ ^ 2 : ℝ) : ℂ)).re = ‖u‖ ^ 2 := Complex.ofReal_re _
    exact le_trans (le_of_eq e.symm) h
  have h3 : S ^ 2 ≤ M * S * ‖v‖ ^ 2 := by
    calc S ^ 2 ≤ (‖u‖ * ‖v‖) ^ 2 := pow_le_pow_left₀ hS0 h1 2
      _ = ‖u‖ ^ 2 * ‖v‖ ^ 2 := by ring
      _ ≤ M * S * ‖v‖ ^ 2 := mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
  rcases hS0.eq_or_lt with h | h
  · rw [← h]; positivity
  · nlinarith

/-- `tr f(A) = ∑_k f(λ_k)` for a Hermitian matrix and the functional calculus. -/
theorem trace_cfc_eq_sum {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    trace (cfc f A) = ∑ k, ((f (hA.eigenvalues k) : ℝ) : ℂ) := by
  rw [hA.cfc_eq, IsHermitian.cfc, Unitary.conjStarAlgAut_apply, trace_mul_cycle,
    Unitary.coe_star_mul_self, Matrix.one_mul, trace_diagonal]
  rfl

/-- **Lemma 6.1**: for vectors `v, w_1, …, w_m` of a complex inner product space and the
Gram matrix `A_{ij} = ⟨w_i, w_j⟩`, for every real `p ≥ 1`,
`∑_i |⟨v, w_i⟩|² ≤ ‖v‖² (tr A^p)^{1/p}`, where `A^p` is the functional calculus power. -/
theorem sum_norm_inner_sq_le_trace_rpow (v : E) (w : ι → E) {p : ℝ} (hp : 1 ≤ p) :
    ∑ i, ‖inner ℂ v (w i)‖ ^ 2
      ≤ ‖v‖ ^ 2 * (trace (cfc (fun x : ℝ => x ^ p) (gram ℂ w))).re ^ (1 / p) := by
  have hA := (posSemidef_gram ℂ w).isHermitian
  have hev : ∀ k, 0 ≤ hA.eigenvalues k := (posSemidef_gram ℂ w).eigenvalues_nonneg
  have htr : (trace (cfc (fun x : ℝ => x ^ p) (gram ℂ w))).re = ∑ k, hA.eigenvalues k ^ p := by
    rw [trace_cfc_eq_sum hA, Complex.re_sum]
    simp
  rw [htr]
  have hp0' : 0 < p := by linarith
  have hp0 : p ≠ 0 := hp0'.ne'
  refine sum_norm_inner_sq_le_of_eigenvalues_le v w
    (Real.rpow_nonneg (Finset.sum_nonneg fun k _ => Real.rpow_nonneg (hev k) p) _) fun j => ?_
  calc hA.eigenvalues j = (hA.eigenvalues j ^ p) ^ (1 / p) := by
        rw [one_div, Real.rpow_rpow_inv (hev j) hp0]
    _ ≤ (∑ k, hA.eigenvalues k ^ p) ^ (1 / p) := by
        refine Real.rpow_le_rpow (Real.rpow_nonneg (hev j) p) ?_ (one_div_nonneg.mpr hp0'.le)
        exact Finset.single_le_sum (f := fun k => hA.eigenvalues k ^ p)
          (fun k _ => Real.rpow_nonneg (hev k) p) (Finset.mem_univ j)

/-- **Lemma 6.1** for integer `p ≥ 1`, with the ordinary matrix power:
`∑_i |⟨v, w_i⟩|² ≤ ‖v‖² (tr A^p)^{1/p}`. -/
theorem sum_norm_inner_sq_le_trace_pow (v : E) (w : ι → E) {p : ℕ} (hp : 1 ≤ p) :
    ∑ i, ‖inner ℂ v (w i)‖ ^ 2 ≤ ‖v‖ ^ 2 * (trace (gram ℂ w ^ p)).re ^ (1 / (p : ℝ)) := by
  have hA := (posSemidef_gram ℂ w).isHermitian
  have h := sum_norm_inner_sq_le_trace_rpow v w (p := p) (by exact_mod_cast hp)
  have hcfc : cfc (fun x : ℝ => x ^ (p : ℝ)) (gram ℂ w) = gram ℂ w ^ p := by
    simp_rw [Real.rpow_natCast]
    exact cfc_pow_id (gram ℂ w) p hA
  rwa [hcfc] at h

end Gram

end RBM

