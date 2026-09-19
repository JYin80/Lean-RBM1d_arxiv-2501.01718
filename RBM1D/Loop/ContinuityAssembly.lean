/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Loop.Split
import RBM1D.Loop.Continuity
import RBM1D.Flow.Hypotheses

/-!
# The assembly of §6: Lemma 5.1 (continuity estimate on loops)

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, pp. 51–52 (Lemma 5.1, (5.5)–(5.7))
and pp. 74–76 (§6).  `Loop/Continuity.lean` (T50) has the deterministic skeleton (6.3), (6.5),
(6.7)–(6.9), (6.12) and the `z̃` arithmetic; `Loop/Split.lean` (T44) has Lemma 6.1 and (6.4).
This file puts them together.

## Deterministic part (fixed Hermitian `H`, `Im z, Im w > 0`)

* `IsGLoopProd`, `norm_trace_smul_sub_pow_mul_le`: `|tr((c(Z₊ - Z₋))^j R)| ≤ (2|c|)^j max|L^{(jq+r)}|`
  for loop products `Z_±` of length `q` and `R` of length `r` — "`(2i Im z/W)^p tr A^p` is a
  sum of `2^p` loops of length `p(2(m-l)+1)`".
* `exists_conjTranspose_mul_Eblk`: Ward for the Gram matrix, `Y†Y E_b = (2i Im w)⁻¹(Z₊ - Z₋)`.
* `trace_gram_blockCols_pow`: `tr A^p = W^p tr((Y†Y E_b)^p)` for the Gram matrix
  `A_{jj'} = ⟨w_j, w_{j'}⟩`, `w_j = Y_{·j}`, `j ∈ I_b`.
* `trace_gram_rpow_le`: `(tr A^p)^{1/p} ≤ W (Im w)⁻¹ (max|L_w^{(p(2k-1))}|)^{1/p}`.
* `sum_norm_gchain_row_sq_le`: **(6.12)** as an inequality,
  `W⁻¹ ∑_{i∈I_{a₀}} ‖v^{(l)}‖² ≤ (Im z)⁻¹ max|L_z^{(2l-1)}|`.
* `wmass_gchain_mul_gchain_le`, `wmass_gchainMixed_le`: **(6.10)** summed over `i`, `j`.
* `norm_gloop_symIdx_le_tilde`, `loopMax_two_mul_le_tilde`: **(6.11)**,
  `max|L_z^{(2m)}| ≤ (m+1)(max|L_w^{(2m)}| + |z-w|²/(Im z Im w)
    ∑_{l<m} max|L_z^{(2l+1)}| (max|L_w^{(p(2(m-l)-1))}|)^{1/p})`.
* `loopMax_one_le`: the base case **(5.6)**: `|G_{ii}| ≤ 2` gives `max|L^{(1)}| ≤ 2`.

## Stochastic part

* Closure properties of `≺` used by §6: `StochDom.mono_right_eventually`,
  `StochDom.rpow_of_le_one`, `StochDom.sqrt_of`, `StochDom.finset_sum_of`,
  `StochDom.det_mul_of`, `StochDom.of_forall_rpow_mul` (`ξ ≺ N^δ ζ` for all `δ > 0` gives
  `ξ ≺ ζ`, used to absorb `(Wℓη)^{1/p}`), and the final step
  `StochDom.of_le_add_sqrt_mul`: **`X ≺ A + A^{1/2}X^{1/2} ⟹ X ≺ A`**.
* `StochDom.odd_of_even`: (6.4) under `≺`.
* `StochDom.continuity_recursion`: **the induction of §6** ((6.6) via (6.13)), for abstract
  families `Y_n` (`= 1_Ω max|L_{t₂}^{(n)}|`) and `T_n` (`= max|L̃^{(n)}|`).
* `LoopScaling`: **(6.1)** as a hypothesis (a transfer of `≺`-bounds, not a postulate).
* `Sample.gmaxEvent`: the event (5.6) `Ω = {‖G_{t₂}‖_max ≤ 2}`.
* `lemma_5_1`: **Lemma 5.1**, `1_Ω max_{σ,a}|L_{t₂,σ,a}| ≺ (Wℓ₁η₂)^{-n+1}`;
  `lemma_5_1'`: the same with the right side `(ℓ₂/ℓ₁)^{n-1}(Wℓ₂η₂)^{-n+1}` of (5.7).

## Deviations from the paper

* (6.1) is the hypothesis `LoopScaling`: `≺`-bounds (deterministic control) on the loops of
  `G_{t₁}` transfer to the loops of `G̃ = (H_{t₂} - z̃_{t₁})⁻¹`.  Hypothesis (5.5) is taken
  with its right side `(Wℓ₁η₁)^{-n+1}` literally, for every `n ≥ 1`.
* Times: `c ≤ t₁ ≤ t₂ < 1` (the paper: `c < t₁ ≤ t₂ ≤ 1`; `t₂ = 1` makes `G_{t₂}` undefined),
  and `|E| ≤ 2 - κ` (bulk, implicit in the paper; needed for `|z_{t₂} - z̃|² ≤ Cη₁²`).
* The indicator `1_Ω` is `Set.indicator` of `Sample.gmaxEvent`; the maximum over `(σ, a)` is
  the uniformity of `≺` in the parameter `u ∈ LoopData`.
* (6.9)'s `C_m` is `m + 1`.  The paper's "`2^p` loops" are handled by expanding one factor of
  `A^p` at a time (`norm_trace_smul_sub_pow_mul_le`), never writing the `2^p` loops out.
  The Gram matrix is indexed by `Fin W` (the offsets of the block `I_{a_m}`), and `A^p` is the
  matrix power (`p ∈ ℕ`, `p ≥ 1`), via `sum_norm_inner_sq_le_trace_pow`.
* "Take `p` large so that `1/p` is absorbed by `≺`" is made precise as: the loss is
  `(Wℓ₁η₁)^{1/p} ≤ N^{1/p}` (as `Wℓ₁η₁ ≤ WL ≤ N`), and `ξ ≺ N^δ ζ` for every `δ > 0` implies
  `ξ ≺ ζ` (`StochDom.of_forall_rpow_mul`); for given `δ` the proof picks `p` with `2/p < δ`.
* The induction is on even lengths `2m` (strong induction), with the odd lengths `2l+1`,
  `l ≤ m-2`, from (6.4) and the base case (5.6) for `l = 0`; for `m > 1` the term `l = m - 1`
  of (6.13) is bounded via (6.4) by `A^{1/2}X^{1/2}` exactly as on p. 76.  Symmetric loops are
  `symIdx` of `Loop/Split.lean` (`⟨C E_{b'} C† E_b⟩`, a rotation of the paper's (6.5)).
-/

namespace RBM

open Matrix

section LoopProd

variable {L W : ℕ} [NeZero L] [NeZero W] {H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ}
  {z : ℂ}

variable (L W) in
/-- `M` is the loop product `∏_i G(σ_i) E_{a_i}` of some loop index of length `r`. -/
def IsGLoopProd (H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (z : ℂ) (r : ℕ)
    (M : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) : Prop :=
  ∃ I : LoopIdx (ZMod L), I.σ.length = r ∧ I.a.length = r ∧ M = gloopProd L W H z I

theorem isGLoopProd_one : IsGLoopProd L W H z 0 1 :=
  ⟨⟨[], []⟩, rfl, rfl, gloopProd_nil.symm⟩

theorem IsGLoopProd.mul {r r' : ℕ} {M M' : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ}
    (h : IsGLoopProd L W H z r M) (h' : IsGLoopProd L W H z r' M') :
    IsGLoopProd L W H z (r + r') (M * M') := by
  obtain ⟨⟨σ, a⟩, hσ, ha, rfl⟩ := h
  obtain ⟨⟨σ', a'⟩, hσ', ha', rfl⟩ := h'
  refine ⟨⟨σ ++ σ', a ++ a'⟩, by simp_all, by simp_all, ?_⟩
  exact (gloopProd_append (by simp_all) σ' a').symm

omit [NeZero W] in
theorem IsGLoopProd.norm_trace_le {r : ℕ} {M : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ}
    (h : IsGLoopProd L W H z r M) : ‖trace M‖ ≤ loopMax L W H z r := by
  obtain ⟨I, hσ, ha, rfl⟩ := h
  exact norm_gloop_le_loopMax I hσ ha

/-- The trace of a power of `c(Z₊ - Z₋)`, `Z_±` loop products of length `q`, times a loop
product of length `r`, is bounded by `(2|c|)^j max|L^{(jq+r)}|`: expand one factor at a time. -/
theorem norm_trace_smul_sub_pow_mul_le {q : ℕ} {Zp Zm : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ}
    (hp : IsGLoopProd L W H z q Zp) (hm : IsGLoopProd L W H z q Zm) {c : ℂ} {β : ℝ}
    (hβ : 2 * ‖c‖ ≤ β) (j : ℕ) :
    ∀ {r : ℕ} {R : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ}, IsGLoopProd L W H z r R →
      ‖trace ((c • (Zp - Zm)) ^ j * R)‖ ≤ β ^ j * loopMax L W H z (j * q + r) := by
  have hβ0 : 0 ≤ β := le_trans (by positivity) hβ
  induction j with
  | zero =>
    intro r R hR
    simpa using hR.norm_trace_le
  | succ j ih =>
    intro r R hR
    have e : (j + 1) * q + r = j * q + (q + r) := by ring
    rw [pow_succ, Matrix.mul_assoc, Matrix.smul_mul, Matrix.sub_mul, Matrix.mul_smul,
      Matrix.mul_sub, trace_smul, trace_sub, e, norm_smul]
    have h1 := ih (hp.mul hR)
    have h2 := ih (hm.mul hR)
    calc ‖c‖ * ‖trace ((c • (Zp - Zm)) ^ j * (Zp * R)) - trace ((c • (Zp - Zm)) ^ j * (Zm * R))‖
        ≤ ‖c‖ * (β ^ j * loopMax L W H z (j * q + (q + r))
            + β ^ j * loopMax L W H z (j * q + (q + r))) :=
          mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add h1 h2)) (norm_nonneg _)
      _ = (2 * ‖c‖) * (β ^ j * loopMax L W H z (j * q + (q + r))) := by ring
      _ ≤ β * (β ^ j * loopMax L W H z (j * q + (q + r))) :=
          mul_le_mul_of_nonneg_right hβ (mul_nonneg (pow_nonneg hβ0 _) (loopMax_nonneg _))
      _ = _ := by ring

end LoopProd

section Ward

variable {L W : ℕ} [NeZero L] [NeZero W] {H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ}
  {z : ℂ}

/-- The matrix form of closing a half-chain around `G(s)`:
`Q G(s) Q† E_{a₀} = ∏ G E` over the index `(ρ, s, \bar ρ^{rev}), (b, b^{rev}, a₀)`. -/
theorem gloopProd_Gsig_conjTranspose_Eblk (hH : H.IsHermitian) {ρ : List Bool}
    {b : List (ZMod L)} (h : ρ.length = b.length) (s : Bool) (a0 : ZMod L) :
    gloopProd L W H z ⟨ρ, b⟩ * Gsig H z s * (gloopProd L W H z ⟨ρ, b⟩)ᴴ * Eblk L W a0
      = gloopProd L W H z ⟨ρ ++ s :: (ρ.map (!·)).reverse, b ++ (b.reverse ++ [a0])⟩ := by
  have hG : Gsig H z s * (gloopProd L W H z ⟨ρ, b⟩)ᴴ
      = gchain L W H z (s :: (ρ.map (!·)).reverse) b.reverse := by
    have hc := gchain_conjTranspose (H := H) (z := z) (L := L) (W := W) hH
      (tau := ρ ++ [!s]) (a := b) (by simpa using h)
    rw [gchain_append_singleton h, Matrix.conjTranspose_mul, Gsig_conjTranspose hH,
      Bool.not_not] at hc
    rw [hc]
    simp
  have h' : (s :: (ρ.map (!·)).reverse).length = b.reverse.length + 1 := by simpa using h
  rw [Matrix.mul_assoc (gloopProd L W H z ⟨ρ, b⟩), hG, Matrix.mul_assoc, gchain_mul_Eblk h',
    ← gloopProd_append h]

/-- **Ward's identity for the Gram matrix of (6.10).**  For a chain `Y` with `k` resolvents,
`Y† Y E_b = (2i Im z)⁻¹ (Z₊ - Z₋)` with `Z_±` loop products of length `2k - 1`. -/
theorem exists_conjTranspose_mul_Eblk (hH : H.IsHermitian) (hz : z.im ≠ 0) {τ : List Bool}
    {c : List (ZMod L)} (h : τ.length = c.length + 1) (b : ZMod L) :
    ∃ Zp Zm : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ,
      IsGLoopProd L W H z (2 * τ.length - 1) Zp ∧ IsGLoopProd L W H z (2 * τ.length - 1) Zm ∧
      (gchain L W H z τ c)ᴴ * gchain L W H z τ c * Eblk L W b
        = (2 * Complex.I * (z.im : ℂ))⁻¹ • (Zp - Zm) := by
  have hY := gchain_conjTranspose (H := H) (z := z) (L := L) (W := W) hH h
  set τ' := (τ.map (!·)).reverse with hτ'
  have hlen : τ'.length = τ.length := by simp [hτ']
  rcases List.eq_nil_or_concat' τ' with h0 | ⟨ρ, s, hρ⟩
  · rw [h0] at hlen; simp at hlen; omega
  have hρτ : ρ.length + 1 = τ.length := by
    have := congrArg List.length hρ
    rw [List.length_append, List.length_singleton] at this
    omega
  have hρlen : ρ.length = c.reverse.length := by
    rw [List.length_reverse]; omega
  have hQ : gchain L W H z τ' c.reverse = gloopProd L W H z ⟨ρ, c.reverse⟩ * Gsig H z s := by
    rw [hρ, gchain_append_singleton hρlen]
  set Q := gloopProd L W H z ⟨ρ, c.reverse⟩
  have hY2 : gchain L W H z τ c = (Q * Gsig H z s)ᴴ := by
    rw [← hQ, ← hY, conjTranspose_conjTranspose]
  have hYY : (gchain L W H z τ c)ᴴ * gchain L W H z τ c
      = Q * (Gsig H z s * (Gsig H z s)ᴴ) * Qᴴ := by
    rw [hY2, conjTranspose_conjTranspose, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  have hW := Gsig_mul_conjTranspose (z := z) hH (isUnit_sub_smul_one_of_im_ne_zero hH hz)
    (isUnit_sub_smul_one_of_im_ne_zero hH (by simpa using hz)) s
  have hc : (2 * Complex.I * (z.im : ℂ)) ≠ 0 := by simp [Complex.I_ne_zero, hz]
  have hGG : Gsig H z s * (Gsig H z s)ᴴ
      = (2 * Complex.I * (z.im : ℂ))⁻¹ • (Gsig H z true - Gsig H z false) := by
    rw [← hW, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have hlen2 : ∀ t : Bool, (ρ ++ t :: (ρ.map (!·)).reverse).length = 2 * τ.length - 1 := by
    intro t; simp; omega
  have hlen3 : (c.reverse ++ (c.reverse.reverse ++ [b])).length = 2 * τ.length - 1 := by
    simp; omega
  refine ⟨_, _,
    ⟨⟨ρ ++ true :: (ρ.map (!·)).reverse, c.reverse ++ (c.reverse.reverse ++ [b])⟩,
      hlen2 true, hlen3, rfl⟩,
    ⟨⟨ρ ++ false :: (ρ.map (!·)).reverse, c.reverse ++ (c.reverse.reverse ++ [b])⟩,
      hlen2 false, hlen3, rfl⟩, ?_⟩
  rw [← gloopProd_Gsig_conjTranspose_Eblk hH hρlen, ← gloopProd_Gsig_conjTranspose_Eblk hH hρlen,
    hYY, hGG, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.sub_mul]

/-- **(6.12) as an inequality**: `W⁻¹ ∑_{i ∈ I_{a₀}} ‖v^{(l)}‖² ≤ (Im z)⁻¹ max|L^{(2l-1)}|`,
where `v^{(l)}` is the row `i` of a chain with `l` resolvents. -/
theorem sum_norm_gchain_row_sq_le (hH : H.IsHermitian) (hz : 0 < z.im) {ρ : List Bool}
    {b : List (ZMod L)} (h : ρ.length = b.length) (s : Bool) (a0 : ZMod L) :
    (W : ℝ)⁻¹ * ∑ α : Fin W, ∑ k : ZMod L × Fin W, ‖gchain L W H z (ρ ++ [s]) b (a0, α) k‖ ^ 2
      ≤ (z.im)⁻¹ * loopMax L W H z (2 * ρ.length + 1) := by
  have hw := ward_chain_row' (H := H) hH hz.ne' h s a0
  set S : ℝ := (W : ℝ)⁻¹ * ∑ α : Fin W, ∑ k : ZMod L × Fin W,
    ‖gchain L W H z (ρ ++ [s]) b (a0, α) k‖ ^ 2 with hS
  have hS0 : 0 ≤ S := by positivity
  have hSC : (S : ℂ) = (W : ℂ)⁻¹ * ∑ α : Fin W, ∑ k : ZMod L × Fin W,
      (Complex.normSq (gchain L W H z (ρ ++ [s]) b (a0, α) k) : ℂ) := by
    rw [hS]
    simp only [← Complex.sq_norm]
    push_cast
    rfl
  have hlen : ∀ t : Bool, (ρ ++ t :: (ρ.map (!·)).reverse).length = 2 * ρ.length + 1 := by
    intro t; simp; ring
  have hlen' : (b ++ (b.reverse ++ [a0])).length = 2 * ρ.length + 1 := by simp [h]; ring
  have h1 := norm_gloop_le_loopMax (L := L) (W := W) (H := H) (z := z)
    ⟨ρ ++ true :: (ρ.map (!·)).reverse, b ++ (b.reverse ++ [a0])⟩ (hlen true) hlen'
  have h2 := norm_gloop_le_loopMax (L := L) (W := W) (H := H) (z := z)
    ⟨ρ ++ false :: (ρ.map (!·)).reverse, b ++ (b.reverse ++ [a0])⟩ (hlen false) hlen'
  have hnc : ‖(2 * Complex.I * (z.im : ℂ))⁻¹‖ = (2 * z.im)⁻¹ := by
    rw [norm_inv, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_of_nonneg hz.le]
    norm_num
  calc S = ‖(S : ℂ)‖ := by rw [Complex.norm_real, Real.norm_of_nonneg hS0]
    _ = ‖(2 * Complex.I * (z.im : ℂ))⁻¹‖ * ‖gloop L W H z
          ⟨ρ ++ true :: (ρ.map (!·)).reverse, b ++ (b.reverse ++ [a0])⟩
        - gloop L W H z ⟨ρ ++ false :: (ρ.map (!·)).reverse, b ++ (b.reverse ++ [a0])⟩‖ := by
        rw [hSC, hw, norm_mul]
    _ ≤ (2 * z.im)⁻¹ * (loopMax L W H z (2 * ρ.length + 1)
          + loopMax L W H z (2 * ρ.length + 1)) := by
        rw [hnc]
        exact mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add h1 h2))
          (by positivity)
    _ = _ := by field_simp; ring

end Ward

section Gram

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- The columns `Y_{·,(b,β)}`, `β ∈ Fin W`, of a matrix, as vectors of `ℓ²`: the vectors
`w^{(l)}_j`, `j ∈ I_b`, of (6.10). -/
noncomputable def blockCols (Y : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (b : ZMod L) :
    Fin W → EuclideanSpace ℂ (ZMod L × Fin W) :=
  fun β => WithLp.toLp 2 (fun k => Y k (b, β))

/-- The selection matrix `R_{x,β} = 1(x = (b,β))` of the block `I_b`. -/
noncomputable def blockSel (b : ZMod L) : Matrix (ZMod L × Fin W) (Fin W) ℂ :=
  Matrix.of fun x β => if x = (b, β) then 1 else 0

omit [NeZero W] in
theorem gram_blockCols (Y : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (b : ZMod L) :
    gram ℂ (blockCols Y b) = (blockSel b)ᵀ * (Yᴴ * Y) * blockSel b := by
  ext β β'
  simp [gram_apply, blockCols, PiLp.inner_apply, blockSel, Matrix.mul_apply, mul_comm]

omit [NeZero L] in
theorem blockSel_mul_transpose (b : ZMod L) :
    blockSel (W := W) b * (blockSel b)ᵀ = (W : ℂ) • Eblk L W b := by
  ext x y
  simp only [blockSel, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Eblk,
    Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul]
  by_cases hxy : x = y
  · subst hxy
    by_cases hx : x.1 = b
    · rw [Finset.sum_eq_single x.2]
      · simp [hx, Prod.ext_iff]
      · intro β _ hβ; simp [Prod.ext_iff, hβ.symm]
      · simp
    · simp [hx, Prod.ext_iff]
  · rw [ite_eq_right_iff.mpr (fun h => absurd h hxy)]
    simp only [mul_ite, mul_one, mul_zero]
    refine Finset.sum_eq_zero fun β _ => ?_
    split_ifs with h1 h2 <;> first | rfl | exact absurd (h1.trans h2.symm) hxy | exact absurd (h1.trans h2.symm).symm hxy

omit [NeZero W] in
theorem transpose_blockSel_mul (b : ZMod L) :
    (blockSel (W := W) b)ᵀ * blockSel (W := W) b = 1 := by
  ext β β'
  simp [blockSel, Matrix.mul_apply, Matrix.one_apply, eq_comm]

theorem trace_transpose_mul_mul_pow_succ {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (R : Matrix m n ℂ) (K : Matrix m m ℂ) (p : ℕ) :
    trace ((Rᵀ * K * R) ^ (p + 1)) = trace ((K * (R * Rᵀ)) ^ (p + 1)) := by
  have key : ∀ p : ℕ, (Rᵀ * K * R) ^ (p + 1) = Rᵀ * ((K * (R * Rᵀ)) ^ p * K * R) := by
    intro p
    induction p with
    | zero => simp [Matrix.mul_assoc]
    | succ p ih =>
      rw [pow_succ, ih, pow_succ]
      simp only [Matrix.mul_assoc]
  rw [key, trace_mul_comm, pow_succ]
  simp only [Matrix.mul_assoc]

/-- `tr (A^{p+1}) = W^{p+1} tr ((Y†Y E_b)^{p+1})` for the Gram matrix `A` of the block
columns of `Y` (the identity behind "`(2i Im z / W)^p tr A^p` is a sum of loops" in §6). -/
theorem trace_gram_blockCols_pow (Y : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (b : ZMod L)
    (p : ℕ) :
    trace (gram ℂ (blockCols Y b) ^ (p + 1))
      = (W : ℂ) ^ (p + 1) * trace ((Yᴴ * Y * Eblk L W b) ^ (p + 1)) := by
  rw [gram_blockCols, trace_transpose_mul_mul_pow_succ, blockSel_mul_transpose, Matrix.mul_smul,
    smul_pow, trace_smul, smul_eq_mul]

omit [NeZero W] in
/-- `∑_i bw_b(i) f(i) = W⁻¹ ∑_{α} f(b, α)`. -/
theorem sum_bw_mul (b : ZMod L) (f : ZMod L × Fin W → ℝ) :
    ∑ i, bw b i * f i = (W : ℝ)⁻¹ * ∑ α : Fin W, f (b, α) := by
  rw [Fintype.sum_prod_type, Finset.sum_eq_single b]
  · simp [bw, Finset.mul_sum]
  · intro c _ hc; simp [bw, hc]
  · simp

end Gram

section Six10

variable {L W : ℕ} [NeZero L] [NeZero W] {H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ}

/-- The `ℓ²` bound on the Gram matrix of (6.10): for a chain `Y` with `k` resolvents at `w`
and `p ≥ 1`, `(tr A^p)^{1/p} ≤ W (Im w)⁻¹ (max|L_w^{(p(2k-1))}|)^{1/p}`. -/
theorem trace_gram_rpow_le (hH : H.IsHermitian) {w : ℂ} (hw : 0 < w.im) {τ : List Bool}
    {c : List (ZMod L)} (h : τ.length = c.length + 1) (b : ZMod L) {p : ℕ} (hp : 1 ≤ p) :
    (trace (gram ℂ (blockCols (gchain L W H w τ c) b) ^ p)).re ^ (1 / (p : ℝ))
      ≤ (W : ℝ) * (w.im)⁻¹ * loopMax L W H w (p * (2 * τ.length - 1)) ^ (1 / (p : ℝ)) := by
  obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
  set Y := gchain L W H w τ c
  set LM := loopMax L W H w ((p' + 1) * (2 * τ.length - 1))
  obtain ⟨Zp, Zm, hZp, hZm, hK⟩ := exists_conjTranspose_mul_Eblk hH hw.ne' h b
  have hc : 2 * ‖(2 * Complex.I * (w.im : ℂ))⁻¹‖ ≤ (w.im)⁻¹ := by
    rw [norm_inv, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
      Real.norm_of_nonneg hw.le]
    field_simp
    norm_num
  have hb : ‖trace ((Yᴴ * Y * Eblk L W b) ^ (p' + 1))‖ ≤ (w.im)⁻¹ ^ (p' + 1) * LM := by
    rw [hK]
    have := norm_trace_smul_sub_pow_mul_le hZp hZm hc (p' + 1) (isGLoopProd_one (L := L) (W := W)
      (H := H) (z := w))
    simpa using this
  have hW0 : (0 : ℝ) < W := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
  have hLM : 0 ≤ LM := loopMax_nonneg _
  have hnorm : ‖trace (gram ℂ (blockCols Y b) ^ (p' + 1))‖
      ≤ ((W : ℝ) * (w.im)⁻¹) ^ (p' + 1) * LM := by
    rw [trace_gram_blockCols_pow, norm_mul, norm_pow, Complex.norm_natCast, mul_pow,
      mul_assoc ((W : ℝ) ^ (p' + 1))]
    exact mul_le_mul_of_nonneg_left hb (by positivity)
  have hp0 : ((p' + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  set x := (trace (gram ℂ (blockCols Y b) ^ (p' + 1))).re
  calc x ^ (1 / ((p' + 1 : ℕ) : ℝ)) ≤ |x ^ (1 / ((p' + 1 : ℕ) : ℝ))| := le_abs_self _
    _ ≤ |x| ^ (1 / ((p' + 1 : ℕ) : ℝ)) := Real.abs_rpow_le_abs_rpow _ _
    _ ≤ (((W : ℝ) * (w.im)⁻¹) ^ (p' + 1) * LM) ^ (1 / ((p' + 1 : ℕ) : ℝ)) :=
        Real.rpow_le_rpow (abs_nonneg _) ((Complex.abs_re_le_norm _).trans hnorm)
          (by positivity)
    _ = (W : ℝ) * (w.im)⁻¹ * LM ^ (1 / ((p' + 1 : ℕ) : ℝ)) := by
        rw [Real.mul_rpow (by positivity) hLM, one_div,
          Real.pow_rpow_inv_natCast (by positivity) (by omega)]

/-- **(6.10)** summed over the rows, with the Ward identities (6.12) and (Gram).  For the
mixed chain `M = X·Y`, `X` a chain of `l` resolvents at `z` (ending in `G_l`) and `Y` a chain of
`k` resolvents at `w` (starting with `G̃_l`),
\[ \sum_{i\in I_{a_0}, j\in I_{a_m}} W^{-2}|M_{ij}|^2
    \le (\operatorname{Im} z\operatorname{Im} w)^{-1}\max|\mathcal L_z^{(2l-1)}|
      \bigl(\max|\mathcal L_w^{(p(2k-1))}|\bigr)^{1/p}. \] -/
theorem wmass_gchain_mul_gchain_le (hH : H.IsHermitian) {z w : ℂ} (hz : 0 < z.im)
    (hw : 0 < w.im) {ρ : List Bool} {b₁ : List (ZMod L)} (h₁ : ρ.length = b₁.length) (s : Bool)
    {τ : List Bool} {c : List (ZMod L)} (h₂ : τ.length = c.length + 1) {p : ℕ} (hp : 1 ≤ p)
    (a0 am : ZMod L) :
    wmass (bw a0) (bw am) (gchain L W H z (ρ ++ [s]) b₁ * gchain L W H w τ c)
      ≤ (z.im * w.im)⁻¹ * loopMax L W H z (2 * ρ.length + 1)
        * loopMax L W H w (p * (2 * τ.length - 1)) ^ (1 / (p : ℝ)) := by
  set X := gchain L W H z (ρ ++ [s]) b₁
  set Y := gchain L W H w τ c
  set M := X * Y
  set T := (trace (gram ℂ (blockCols Y am) ^ p)).re ^ (1 / (p : ℝ))
  set v : Fin W → EuclideanSpace ℂ (ZMod L × Fin W) :=
    fun α => WithLp.toLp 2 (fun k => star (X (a0, α) k))
  have hinner : ∀ α β, inner ℂ (v α) (blockCols Y am β) = M (a0, α) (am, β) := by
    intro α β
    simp [v, blockCols, PiLp.inner_apply, M, Matrix.mul_apply, mul_comm]
  have hv : ∀ α, ‖v α‖ ^ 2 = ∑ k, ‖X (a0, α) k‖ ^ 2 := by
    intro α
    rw [EuclideanSpace.norm_sq_eq]
    simp [v]
  have h61 : ∀ α, ∑ β, ‖M (a0, α) (am, β)‖ ^ 2 ≤ (∑ k, ‖X (a0, α) k‖ ^ 2) * T := by
    intro α
    have := sum_norm_inner_sq_le_trace_pow (v α) (blockCols Y am) hp
    simp_rw [hinner, hv] at this
    exact this
  have hT := trace_gram_rpow_le hH hw h₂ am hp
  have hrow := sum_norm_gchain_row_sq_le (W := W) (H := H) hH hz h₁ s a0
  have hW0 : (0 : ℝ) < W := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
  set LMz := loopMax L W H z (2 * ρ.length + 1)
  set LMw := loopMax L W H w (p * (2 * τ.length - 1))
  have hLMw : 0 ≤ LMw ^ (1 / (p : ℝ)) := Real.rpow_nonneg (loopMax_nonneg _) _
  have hS0 : 0 ≤ (W : ℝ)⁻¹ * ∑ α : Fin W, ∑ k, ‖X (a0, α) k‖ ^ 2 := by positivity
  calc wmass (bw a0) (bw am) M
      = ∑ i, bw a0 i * ∑ j, bw am j * ‖M i j‖ ^ 2 := by
        unfold wmass
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
    _ = ∑ i, bw a0 i * ((W : ℝ)⁻¹ * ∑ β : Fin W, ‖M i (am, β)‖ ^ 2) :=
        Finset.sum_congr rfl fun i _ => by rw [sum_bw_mul am (fun j => ‖M i j‖ ^ 2)]
    _ = (W : ℝ)⁻¹ * ∑ α : Fin W, ((W : ℝ)⁻¹ * ∑ β : Fin W, ‖M (a0, α) (am, β)‖ ^ 2) :=
        sum_bw_mul a0 (fun i => (W : ℝ)⁻¹ * ∑ β : Fin W, ‖M i (am, β)‖ ^ 2)
    _ ≤ (W : ℝ)⁻¹ * ∑ α : Fin W, ((W : ℝ)⁻¹ * ((∑ k, ‖X (a0, α) k‖ ^ 2) * T)) := by
        gcongr with α
        exact h61 α
    _ = (W : ℝ)⁻¹ * ((W : ℝ)⁻¹ * ∑ α : Fin W, ∑ k, ‖X (a0, α) k‖ ^ 2) * T := by
        have e : ∀ α : Fin W, (W : ℝ)⁻¹ * ((∑ k, ‖X (a0, α) k‖ ^ 2) * T)
            = (∑ k, ‖X (a0, α) k‖ ^ 2) * ((W : ℝ)⁻¹ * T) := fun α => by ring
        simp_rw [e, ← Finset.sum_mul]
        ring
    _ ≤ (W : ℝ)⁻¹ * ((W : ℝ)⁻¹ * ∑ α : Fin W, ∑ k, ‖X (a0, α) k‖ ^ 2)
          * ((W : ℝ) * (w.im)⁻¹ * LMw ^ (1 / (p : ℝ))) :=
        mul_le_mul_of_nonneg_left hT (mul_nonneg (by positivity) hS0)
    _ ≤ (W : ℝ)⁻¹ * ((z.im)⁻¹ * LMz) * ((W : ℝ) * (w.im)⁻¹ * LMw ^ (1 / (p : ℝ))) := by
        gcongr
    _ = (z.im * w.im)⁻¹ * LMz * LMw ^ (1 / (p : ℝ)) := by
        field_simp

end Six10

section Six11

variable {L W : ℕ} [NeZero L] [NeZero W] {H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ}

/-- The `l`-th mixed chain of (6.8) satisfies the bound (6.10):
`W⁻² ∑_{i ∈ I_b, j ∈ I_{b'}} |(G_1 E ⋯ G_l G̃_l ⋯ G̃_m)_{ij}|²
  ≤ (Im z Im w)⁻¹ max|L_z^{(2l+1)}| (max|L_w^{(p(2(m-l)-1))}|)^{1/p}` (`l` counted from `0`). -/
theorem wmass_gchainMixed_le (hH : H.IsHermitian) {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im)
    {σ : List Bool} {a : List (ZMod L)} (h : σ.length = a.length + 1) {p : ℕ} (hp : 1 ≤ p)
    (b' b : ZMod L) {l : ℕ} (hl : l < σ.length) :
    wmass (bw b) (bw b') (gchainMixed L W H z w σ a l)
      ≤ (z.im * w.im)⁻¹ * (loopMax L W H z (2 * l + 1)
        * loopMax L W H w (p * (2 * (σ.length - l) - 1)) ^ (1 / (p : ℝ))) := by
  have h₁ : (σ.take l).length = (a.take l).length := by simp; omega
  have h₂ : (σ.drop l).length = (a.drop l).length + 1 := by simp; omega
  have key := wmass_gchain_mul_gchain_le (W := W) hH hz hw h₁ σ[l] h₂ hp b b'
  rw [List.take_concat_get' σ l hl] at key
  have e1 : (σ.take l).length = l := by simp; omega
  have e2 : (σ.drop l).length = σ.length - l := by simp
  rw [e1, e2] at key
  rw [gchainMixed, ← mul_assoc]
  exact key

/-- **(6.9) + (6.10) + (6.12) = (6.11)**, one symmetric loop at a time.  For a chain `C` of
`m` resolvents, the symmetric loop `⟨C E_{b'} C† E_b⟩` at `z` is bounded by the one at `w`
plus the error terms of the expansion (6.8):
\[ |\mathcal L_z| \le (m+1)\Bigl(|\mathcal L_w| + \frac{|z-w|^2}{\operatorname{Im}z\,
   \operatorname{Im}w}\sum_{l<m}\max|\mathcal L_z^{(2l+1)}|\,
   \bigl(\max|\mathcal L_w^{(p(2(m-l)-1))}|\bigr)^{1/p}\Bigr). \] -/
theorem norm_gloop_symIdx_le_tilde (hH : H.IsHermitian) {z w : ℂ} (hz : 0 < z.im)
    (hw : 0 < w.im) {σ : List Bool} {a : List (ZMod L)} (h : σ.length = a.length + 1) {p : ℕ}
    (hp : 1 ≤ p) (b' b : ZMod L) :
    ‖gloop L W H z (symIdx σ a b' b)‖
      ≤ (σ.length + 1 : ℝ) * (‖gloop L W H w (symIdx σ a b' b)‖ + ‖z - w‖ ^ 2
        * ((z.im * w.im)⁻¹ * ∑ l ∈ Finset.range σ.length, loopMax L W H z (2 * l + 1)
          * loopMax L W H w (p * (2 * (σ.length - l) - 1)) ^ (1 / (p : ℝ)))) := by
  rw [gloop_symIdx hH h, gloop_symIdx hH h, norm_trace_mul_Eblk_mul_conjTranspose_mul_Eblk,
    norm_trace_mul_Eblk_mul_conjTranspose_mul_Eblk]
  have hent := norm_gchain_apply_sq_le (isUnit_sub_zSig hH hz.ne') (isUnit_sub_zSig hH hw.ne') h
  set u := bw (W := W) b
  set v := bw (W := W) b'
  have hu : ∀ i, 0 ≤ u i := bw_nonneg b
  have hv : ∀ j, 0 ≤ v j := bw_nonneg b'
  set m := σ.length
  set M := gchainMixed L W H z w σ a
  have hswap : ∑ l ∈ Finset.range m, wmass u v (M l)
      = ∑ i, ∑ j, u i * v j * ∑ l ∈ Finset.range m, ‖M l i j‖ ^ 2 := by
    unfold wmass
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
  have hmix : ∑ l ∈ Finset.range m, wmass u v (M l)
      ≤ (z.im * w.im)⁻¹ * ∑ l ∈ Finset.range m, loopMax L W H z (2 * l + 1)
          * loopMax L W H w (p * (2 * (m - l) - 1)) ^ (1 / (p : ℝ)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun l hl =>
      wmass_gchainMixed_le hH hz hw h hp b' b (Finset.mem_range.mp hl)
  calc wmass u v (gchain L W H z σ a)
      ≤ ∑ i, ∑ j, u i * v j * ((m + 1 : ℝ) * (‖gchain L W H w σ a i j‖ ^ 2
          + ‖z - w‖ ^ 2 * ∑ l ∈ Finset.range m, ‖M l i j‖ ^ 2)) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (hent i j) (mul_nonneg (hu i) (hv j))
    _ = (m + 1 : ℝ) * (wmass u v (gchain L W H w σ a)
          + ‖z - w‖ ^ 2 * ∑ l ∈ Finset.range m, wmass u v (M l)) := by
        have e1 : ∀ i j, u i * v j * ((m + 1 : ℝ) * (‖gchain L W H w σ a i j‖ ^ 2
            + ‖z - w‖ ^ 2 * ∑ l ∈ Finset.range m, ‖M l i j‖ ^ 2))
            = (m + 1 : ℝ) * (u i * v j * ‖gchain L W H w σ a i j‖ ^ 2)
              + ((m + 1 : ℝ) * ‖z - w‖ ^ 2) * (u i * v j * ∑ l ∈ Finset.range m, ‖M l i j‖ ^ 2) :=
          fun i j => by ring
        rw [hswap, wmass]
        simp_rw [e1, Finset.sum_add_distrib, ← Finset.mul_sum]
        ring
    _ ≤ _ := by gcongr

/-- **(6.11) for the maxima**: for `m ≥ 1`, `p ≥ 1`,
\[ \max|\mathcal L_z^{(2m)}| \le (m+1)\Bigl(\max|\mathcal L_w^{(2m)}| + \frac{|z-w|^2}
   {\operatorname{Im}z\,\operatorname{Im}w}\sum_{l<m}\max|\mathcal L_z^{(2l+1)}|\,
   \bigl(\max|\mathcal L_w^{(p(2(m-l)-1))}|\bigr)^{1/p}\Bigr). \]
Every loop of length `2m` is controlled by symmetric ones ((5.115)). -/
theorem loopMax_two_mul_le_tilde (hH : H.IsHermitian) {z w : ℂ} (hz : 0 < z.im)
    (hw : 0 < w.im) {m : ℕ} (hm : 1 ≤ m) {p : ℕ} (hp : 1 ≤ p) :
    loopMax L W H z (2 * m)
      ≤ (m + 1 : ℝ) * (loopMax L W H w (2 * m) + ‖z - w‖ ^ 2
        * ((z.im * w.im)⁻¹ * ∑ l ∈ Finset.range m, loopMax L W H z (2 * l + 1)
          * loopMax L W H w (p * (2 * (m - l) - 1)) ^ (1 / (p : ℝ)))) := by
  refine loopMax_le fun I hσ ha => norm_gloop_le_of_symIdx_le hH hm ?_ I hσ ha
  intro σ a hσ' ha' b' b
  have h : σ.length = a.length + 1 := by omega
  refine (norm_gloop_symIdx_le_tilde hH hz hw h hp b' b).trans ?_
  rw [hσ']
  gcongr
  have := norm_gloop_symIdx_le_loopMax (W := W) (H := H) (z := w) h b' b
  rwa [hσ'] at this

end Six11

section StochGeneric

open Filter MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {U : ℕ → Type*}

/-- Enlarging the right side of `≺` (for large `N`). -/
theorem StochDom.mono_right_eventually {ξ ζ ζ' : ∀ N, U N → Ω → ℝ} (h : StochDom P ξ ζ)
    (hle : ∀ᶠ N : ℕ in atTop, ∀ u ω, ζ N u ω ≤ ζ' N u ω) : StochDom P ξ ζ' :=
  StochDom.of_subset h fun τ hτ => ⟨τ, hτ, by
    filter_upwards [hle] with N hN
    rintro ω ⟨u, hu⟩
    exact ⟨u, lt_of_le_of_lt (mul_le_mul_of_nonneg_left (hN u ω)
      (Real.rpow_nonneg (Nat.cast_nonneg N) τ)) hu⟩⟩

/-- Powers `0 < r ≤ 1` preserve `≺`: `ξ ≺ ζ` implies `ξ^r ≺ ζ^r`. -/
theorem StochDom.rpow_of_le_one {ξ ζ : ∀ N, U N → Ω → ℝ} {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hξ : ∀ N u ω, 0 ≤ ξ N u ω) (hζ : ∀ N u ω, 0 ≤ ζ N u ω) (h : StochDom P ξ ζ) :
    StochDom P (fun N u ω => ξ N u ω ^ r) (fun N u ω => ζ N u ω ^ r) :=
  StochDom.of_subset h fun τ hτ => ⟨τ, hτ, by
    filter_upwards [eventually_ge_atTop 1] with N hN1
    rintro ω ⟨u, hu⟩
    refine ⟨u, lt_of_not_ge fun hle => ?_⟩
    have hN : (1 : ℝ) ≤ (N : ℝ) ^ τ := Real.one_le_rpow (by exact_mod_cast hN1) hτ.le
    have h1 : ξ N u ω ^ r ≤ ((N : ℝ) ^ τ * ζ N u ω) ^ r :=
      Real.rpow_le_rpow (hξ N u ω) hle hr0.le
    rw [Real.mul_rpow (by linarith) (hζ N u ω)] at h1
    have h2 : ((N : ℝ) ^ τ) ^ r ≤ (N : ℝ) ^ τ := Real.rpow_le_self_of_one_le hN hr1
    have h3 := mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg (hζ N u ω) r)
    exact absurd hu (not_lt.2 (h1.trans h3))⟩

/-- Square roots preserve `≺`. -/
theorem StochDom.sqrt_of {ξ ζ : ∀ N, U N → Ω → ℝ} (hξ : ∀ N u ω, 0 ≤ ξ N u ω)
    (hζ : ∀ N u ω, 0 ≤ ζ N u ω) (h : StochDom P ξ ζ) :
    StochDom P (fun N u ω => Real.sqrt (ξ N u ω)) (fun N u ω => Real.sqrt (ζ N u ω)) := by
  simp only [Real.sqrt_eq_rpow]
  exact StochDom.rpow_of_le_one (by norm_num) (by norm_num) hξ hζ h

/-- **Absorbing `N^δ`**: if `ξ ≺ N^δ ζ` for every `δ > 0`, then `ξ ≺ ζ`. -/
theorem StochDom.of_forall_rpow_mul {ξ ζ : ∀ N, U N → Ω → ℝ}
    (h : ∀ δ > (0 : ℝ), StochDom P ξ (fun N u ω => (N : ℝ) ^ δ * ζ N u ω)) :
    StochDom P ξ ζ := by
  intro τ hτ D hD
  filter_upwards [h (τ / 2) (half_pos hτ) (τ / 2) (half_pos hτ) D hD] with N hN
  refine (measure_mono ?_).trans hN
  rintro ω ⟨u, hu⟩
  refine ⟨u, ?_⟩
  rwa [← mul_assoc, UnifDetDom.rpow_half_mul_rpow_half N hτ]

/-- The elementary inequality behind the last step of §6: for `s ≥ 0`, `T ≥ 1`,
`s² ≤ T(r² + r s)` implies `s² ≤ 4T²r²`. -/
theorem sq_le_four_mul_of_le_add_mul {s r T : ℝ} (hs : 0 ≤ s) (hT : 1 ≤ T)
    (h : s ^ 2 ≤ T * (r ^ 2 + r * s)) : s ^ 2 ≤ 4 * T ^ 2 * r ^ 2 := by
  rcases le_or_gt s (2 * T * r) with h1 | h1
  · have : s ^ 2 ≤ (2 * T * r) ^ 2 := pow_le_pow_left₀ hs h1 2
    nlinarith
  · have hTr : T * r * s ≤ s ^ 2 / 2 := by nlinarith
    have hr2 : 0 ≤ r ^ 2 := sq_nonneg r
    nlinarith

/-- **The last step of §6**: `X ≺ A + A^{1/2} X^{1/2}` implies `X ≺ A` (for `X, A ≥ 0`). -/
theorem StochDom.of_le_add_sqrt_mul {ξ ζ : ∀ N, U N → Ω → ℝ} (hξ : ∀ N u ω, 0 ≤ ξ N u ω)
    (hζ : ∀ N u ω, 0 ≤ ζ N u ω)
    (h : StochDom P ξ (fun N u ω => ζ N u ω + Real.sqrt (ζ N u ω * ξ N u ω))) :
    StochDom P ξ ζ :=
  StochDom.of_subset h fun τ hτ => ⟨τ / 3, by positivity, by
    filter_upwards [eventually_ge_atTop 1, eventually_le_rpow 4 (by positivity : (0 : ℝ) < τ / 3)]
      with N hN1 h4
    rintro ω ⟨u, hu⟩
    refine ⟨u, lt_of_not_ge fun hle => ?_⟩
    set T := (N : ℝ) ^ (τ / 3)
    have hT1 : 1 ≤ T := by linarith
    have hT3 : T ^ 3 = (N : ℝ) ^ τ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]
      congr 1; push_cast; ring
    set x := ξ N u ω
    set a := ζ N u ω
    have hx := hξ N u ω
    have ha := hζ N u ω
    have hs := Real.sq_sqrt hx
    have hr := Real.sq_sqrt ha
    have key : Real.sqrt x ^ 2 ≤ T * (Real.sqrt a ^ 2 + Real.sqrt a * Real.sqrt x) := by
      rw [hs, hr, ← Real.sqrt_mul ha]; exact hle
    have h4' := sq_le_four_mul_of_le_add_mul (Real.sqrt_nonneg _) hT1 key
    rw [hs, hr] at h4'
    have : 4 * T ^ 2 * a ≤ T ^ 3 * a := by
      have : 4 * T ^ 2 ≤ T ^ 3 := by nlinarith
      exact mul_le_mul_of_nonneg_right this ha
    rw [hT3] at this
    exact absurd hu (not_lt.2 (h4'.trans this))⟩

/-- `≺` is closed under finite sums. -/
theorem StochDom.finset_sum_of {ι : Type*} (s : Finset ι) {ξ ζ : ι → ∀ N, U N → Ω → ℝ}
    (h : ∀ i ∈ s, StochDom P (ξ i) (ζ i)) :
    StochDom P (fun N u ω => ∑ i ∈ s, ξ i N u ω) (fun N u ω => ∑ i ∈ s, ζ i N u ω) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h0 := StochDom.refl (P := P) (ζ := fun (N : ℕ) (_ : U N) (_ : Ω) => (0 : ℝ))
      (fun _ _ _ => le_rfl)
    simpa using h0
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

end StochGeneric

section Recursion

open Filter MeasureTheory

/-- `(x^{pj-1})^{1/p} ≤ x^j M^{1/p}` for `x > 0`, `x⁻¹ ≤ M`: the loss `(Wℓη)^{1/p}` of (6.10). -/
theorem rpow_pow_mul_sub_one_le {x M : ℝ} (hx : 0 < x) (hM : x⁻¹ ≤ M) {p j : ℕ} (hp : 1 ≤ p)
    (hj : 1 ≤ j) : (x ^ (p * j - 1)) ^ (1 / (p : ℝ)) ≤ x ^ j * M ^ (1 / (p : ℝ)) := by
  have hpj : 1 ≤ p * j := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have e : x ^ (p * j - 1) = (x ^ j) ^ p * x⁻¹ := by
    rw [← pow_mul, mul_comm j p]
    have : x ^ (p * j) = x ^ (p * j - 1) * x := by
      rw [← pow_succ]; congr 1; omega
    rw [this, mul_assoc, mul_inv_cancel₀ hx.ne', mul_one]
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  rw [e, Real.mul_rpow (by positivity) (by positivity), one_div,
    Real.pow_rpow_inv_natCast (by positivity) (by omega)]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hM (by positivity))
    (by positivity)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {U : ℕ → Type*}

/-- Multiplying both sides of `≺` by a deterministic non-negative factor. -/
theorem StochDom.det_mul_of {f : ℕ → ℝ} (hf : ∀ N, 0 ≤ f N) {ξ ζ : ∀ N, U N → Ω → ℝ}
    (hξ : ∀ N u ω, 0 ≤ ξ N u ω) (h : StochDom P ξ ζ) :
    StochDom P (fun N u ω => f N * ξ N u ω) (fun N u ω => f N * ζ N u ω) :=
  StochDom.mul hξ (fun N _ _ => hf N) (StochDom.refl fun N _ _ => hf N) h

/-- **Odd loops from even ones** ((6.4) under `≺`): if `Y_{2l+1}² ≤ Y_{2l} Y_{2l+2}`,
`Y_{2l} ≺ a^{2l-1}` and `Y_{2l+2} ≺ a^{2l+1}`, then `Y_{2l+1} ≺ a^{2l}`. -/
theorem StochDom.odd_of_even {Y : ℕ → ∀ N, U N → Ω → ℝ} {a : ℕ → ℝ} (ha : ∀ N, 0 ≤ a N)
    (hY0 : ∀ n N u ω, 0 ≤ Y n N u ω) {l : ℕ} (hl : 1 ≤ l)
    (hodd : ∀ N u ω, Y (2 * l + 1) N u ω ^ 2 ≤ Y (2 * l) N u ω * Y (2 * l + 2) N u ω)
    (h1 : StochDom P (Y (2 * l)) (fun N _ _ => a N ^ (2 * l - 1)))
    (h2 : StochDom P (Y (2 * l + 2)) (fun N _ _ => a N ^ (2 * l + 1))) :
    StochDom P (Y (2 * l + 1)) (fun N _ _ => a N ^ (2 * l)) := by
  have hm := StochDom.mul (hY0 _) (fun N _ _ => pow_nonneg (ha N) _) h1 h2
  have hs := StochDom.sqrt_of (fun N u ω => mul_nonneg (hY0 _ N u ω) (hY0 _ N u ω))
    (fun N u ω => mul_nonneg (pow_nonneg (ha N) _) (pow_nonneg (ha N) _)) hm
  have e : ∀ N, Real.sqrt (a N ^ (2 * l - 1) * a N ^ (2 * l + 1)) = a N ^ (2 * l) := by
    intro N
    rw [← pow_add, show 2 * l - 1 + (2 * l + 1) = 2 * (2 * l) by omega, pow_mul',
      Real.sqrt_sq (pow_nonneg (ha N) _)]
  refine StochDom.of_le_left (fun N u ω => Real.le_sqrt_of_sq_le (hodd N u ω)) ?_
  simpa only [Pi.mul_apply, e] using hs

/-- **The induction of §6, abstractly.**  Let `Y_n ≥ 0` (the loops at time `t₂` of length
`n`, times `1_Ω`) and `T_n ≥ 0` (the loops of `G̃`) be families with, for deterministic
`0 < a₁ ≤ a` (`a₁ = (Wℓ₁η₁)⁻¹`, `a = (Wℓ₁η₂)⁻¹`) and `K ≥ 0` with `K a₁ ≤ C a`
(`K = |z - z̃|²/(Im z Im z̃)`),
* `T_n ≺ a₁^{n-1}` ((5.5) + (6.1)),
* `Y_1 ≤ 2` ((5.6)),
* `Y_{2l+1}² ≤ Y_{2l} Y_{2l+2}` ((6.4)),
* `Y_{2m} ≤ (m+1)(T_{2m} + K ∑_{l<m} Y_{2l+1} T_{p(2(m-l)-1)}^{1/p})` for all `p ≥ 1` ((6.11)),
* `a₁⁻¹ ≤ N` for large `N` (so that `a₁^{-1/p} ≤ N^{1/p}` is absorbed by `≺`).
Then `Y_n ≺ a^{n-1}` for every `n ≥ 1`: this is (6.6), proved by the induction on `m` of
§6 ((6.13), the base case `m = 1` and the final step `X ≺ A + A^{1/2}X^{1/2} ⟹ X ≺ A`). -/
theorem StochDom.continuity_recursion {Y T : ℕ → ∀ N, U N → Ω → ℝ} {a a1 K : ℕ → ℝ} {C : ℝ}
    (hY0 : ∀ n N u ω, 0 ≤ Y n N u ω) (hT0 : ∀ n N u ω, 0 ≤ T n N u ω)
    (ha1 : ∀ N, 0 < a1 N) (ha1a : ∀ N, a1 N ≤ a N) (hK0 : ∀ N, 0 ≤ K N) (hC : 0 ≤ C)
    (hK : ∀ N, K N * a1 N ≤ C * a N) (hN : ∀ᶠ N : ℕ in atTop, (a1 N)⁻¹ ≤ N)
    (hT : ∀ n, 1 ≤ n → StochDom P (T n) (fun N _ _ => a1 N ^ (n - 1)))
    (hY1 : ∀ N u ω, Y 1 N u ω ≤ 2)
    (hodd : ∀ l, 1 ≤ l → ∀ N u ω,
      Y (2 * l + 1) N u ω ^ 2 ≤ Y (2 * l) N u ω * Y (2 * l + 2) N u ω)
    (hrec : ∀ m, 1 ≤ m → ∀ p, 1 ≤ p → ∀ N u ω, Y (2 * m) N u ω ≤ (m + 1 : ℝ) *
      (T (2 * m) N u ω + K N * ∑ l ∈ Finset.range m,
        Y (2 * l + 1) N u ω * T (p * (2 * (m - l) - 1)) N u ω ^ (1 / (p : ℝ)))) :
    ∀ n, 1 ≤ n → StochDom P (Y n) (fun N _ _ => a N ^ (n - 1)) := by
  have ha0 : ∀ N, 0 < a N := fun N => (ha1 N).trans_le (ha1a N)
  have hY1' : StochDom P (Y 1) (fun N _ _ => a N ^ (2 * 0)) := by
    simp only [mul_zero, pow_zero]
    have h1 := StochDom.refl (P := P) (ζ := fun (N : ℕ) (_ : U N) (_ : Ω) => (1 : ℝ))
      (fun _ _ _ => zero_le_one)
    exact StochDom.of_le_left (fun N u ω => by linarith [hY1 N u ω])
      (StochDom.const_mul_left (c := 2) (by norm_num) (fun _ _ _ => zero_le_one) h1)
  -- the even lengths, by strong induction
  have hE : ∀ m, 1 ≤ m → StochDom P (Y (2 * m)) (fun N _ _ => a N ^ (2 * m - 1)) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
    intro hm
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have hOdd : ∀ l, l < k → StochDom P (Y (2 * l + 1)) (fun N _ _ => a N ^ (2 * l)) := by
      intro l hl
      rcases Nat.eq_zero_or_pos l with rfl | hl0
      · exact hY1'
      · refine StochDom.odd_of_even (fun N => (ha0 N).le) hY0 hl0 (hodd l hl0)
          (ih l (by omega) hl0) ?_
        have := ih (l + 1) (by omega) (by omega)
        rwa [show 2 * (l + 1) = 2 * l + 2 by ring, show 2 * l + 2 - 1 = 2 * l + 1 by omega]
          at this
    rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega]
    refine StochDom.of_forall_rpow_mul fun δ hδ => ?_
    obtain ⟨p0, hp0⟩ := exists_nat_one_div_lt (half_pos hδ)
    set p := p0 + 1 with hp_def
    have hp : 1 ≤ p := by omega
    set r : ℝ := 1 / (p : ℝ) with hr
    have hr0 : 0 < r := by positivity
    have hr1 : r ≤ 1 := by
      rw [hr, div_le_one (by positivity)]; exact_mod_cast hp
    have hrδ : r + r ≤ δ := by
      have : r < δ / 2 := by rw [hr, hp_def]; push_cast; exact hp0
      linarith
    set A : ℕ → ℝ := fun N => a N ^ (2 * k + 1) with hA
    have hA0 : ∀ N, 0 ≤ A N := fun N => pow_nonneg (ha0 N).le _
    have hNr : ∀ N : ℕ, 0 ≤ (N : ℝ) ^ r := fun N => Real.rpow_nonneg (Nat.cast_nonneg N) r
    have hev : ∀ᶠ N : ℕ in atTop, 1 ≤ (N : ℝ) ^ r ∧ (a1 N)⁻¹ ≤ N := by
      filter_upwards [hN, eventually_ge_atTop 1] with N hN1 hN2
      exact ⟨Real.one_le_rpow (by exact_mod_cast hN2) hr0.le, hN1⟩
    -- (R1): the `G̃` loop of length `2m`
    have hR1 : StochDom P (T (2 * (k + 1))) (fun N _ _ => A N * (N : ℝ) ^ r) := by
      refine (hT (2 * (k + 1)) (by omega)).mono_right_eventually ?_
      filter_upwards [hev] with N hN u ω
      rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega]
      calc a1 N ^ (2 * k + 1) ≤ A N := pow_le_pow_left₀ (ha1 N).le (ha1a N) _
        _ ≤ A N * (N : ℝ) ^ r := le_mul_of_one_le_right (hA0 N) hN.1
    -- the `G̃` factors `T^{1/p}`
    have hTr : ∀ j, 1 ≤ j → StochDom P (fun N u ω => K N * T (p * j) N u ω ^ r)
        (fun N _ _ => C * a1 N ^ (j - 1) * a N * (N : ℝ) ^ r) := by
      intro j hj
      have hpj : 1 ≤ p * j := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
      have h1 := StochDom.det_mul_of hK0 (fun N u ω => Real.rpow_nonneg (hT0 _ N u ω) r)
        (StochDom.rpow_of_le_one hr0 hr1 (hT0 (p * j)) (fun N _ _ => pow_nonneg (ha1 N).le _)
          (hT (p * j) hpj))
      refine h1.mono_right_eventually ?_
      filter_upwards [hev] with N hN u ω
      have h2 := rpow_pow_mul_sub_one_le (ha1 N) hN.2 hp hj
      calc K N * (a1 N ^ (p * j - 1)) ^ r ≤ K N * (a1 N ^ j * (N : ℝ) ^ r) :=
            mul_le_mul_of_nonneg_left h2 (hK0 N)
        _ = (K N * a1 N) * a1 N ^ (j - 1) * (N : ℝ) ^ r := by
            rw [show a1 N ^ j = a1 N * a1 N ^ (j - 1) by
              rw [← pow_succ']; congr 1; omega]
            ring
        _ ≤ (C * a N) * a1 N ^ (j - 1) * (N : ℝ) ^ r :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hK N)
              (pow_nonneg (ha1 N).le _)) (hNr N)
        _ = C * a1 N ^ (j - 1) * a N * (N : ℝ) ^ r := by ring
    -- (R2): the terms `l < m - 1`
    have hR2 : StochDom P (fun N u ω => ∑ l ∈ Finset.range k,
          K N * (Y (2 * l + 1) N u ω * T (p * (2 * (k + 1 - l) - 1)) N u ω ^ r))
        (fun N _ _ => ∑ l ∈ Finset.range k, C * A N * (N : ℝ) ^ r) := by
      refine StochDom.finset_sum_of _ fun l hl => ?_
      have hl' := Finset.mem_range.mp hl
      have hj : 1 ≤ 2 * (k + 1 - l) - 1 := by omega
      have h1 := StochDom.mul (fun N u ω => mul_nonneg (hK0 N) (Real.rpow_nonneg (hT0 _ N u ω) r))
        (fun N _ _ => pow_nonneg (ha0 N).le _) (hOdd l hl') (hTr _ hj)
      refine (StochDom.of_le_left (fun N u ω => le_of_eq ?_) h1).mono_right_eventually ?_
      · simp only [Pi.mul_apply]; ring
      · filter_upwards [hev] with N hN u ω
        simp only [Pi.mul_apply]
        have e : 2 * (k + 1 - l) - 1 - 1 = 2 * (k - l) := by omega
        rw [e]
        calc a N ^ (2 * l) * (C * a1 N ^ (2 * (k - l)) * a N * (N : ℝ) ^ r)
            ≤ a N ^ (2 * l) * (C * a N ^ (2 * (k - l)) * a N * (N : ℝ) ^ r) := by
              exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
                  (pow_le_pow_left₀ (ha1 N).le (ha1a N) _) hC) (ha0 N).le) (hNr N))
                (pow_nonneg (ha0 N).le _)
          _ = C * A N * (N : ℝ) ^ r := by
              simp only [hA]
              rw [show 2 * k + 1 = 2 * l + 2 * (k - l) + 1 by omega, pow_succ, pow_add]
              ring
    -- (R3): the term `l = m - 1`
    have hR3 : StochDom P (fun N u ω => K N * (Y (2 * k + 1) N u ω * T p N u ω ^ r))
        (fun N u ω => 2 * C * A N * (N : ℝ) ^ r
          + C * (N : ℝ) ^ r * Real.sqrt (A N * Y (2 * (k + 1)) N u ω)) := by
      have hT1 := hTr 1 le_rfl
      simp only [mul_one, Nat.sub_self, pow_zero] at hT1
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · -- `m = 1`: the base case (5.6)
        have h1 := StochDom.const_mul_left (c := 2) (by norm_num)
          (fun N _ _ => mul_nonneg (mul_nonneg hC (ha0 N).le) (hNr N)) hT1
        refine (StochDom.of_le_left (fun N u ω => ?_) h1).mono_right_eventually ?_
        · have hy := hY1 N u ω
          have hk := mul_nonneg (hK0 N) (Real.rpow_nonneg (hT0 p N u ω) r)
          simp only [mul_zero, zero_add]
          nlinarith
        · filter_upwards with N u ω
          simp only [hA, mul_zero, zero_add, pow_one]
          have h1 : 0 ≤ C * (N : ℝ) ^ r * Real.sqrt (a N * Y (2 * 1) N u ω) :=
            mul_nonneg (mul_nonneg hC (hNr N)) (Real.sqrt_nonneg _)
          have h2 : 0 ≤ C * a N * (N : ℝ) ^ r := mul_nonneg (mul_nonneg hC (ha0 N).le) (hNr N)
          linarith
      · -- `m > 1`: (6.4) and the induction hypothesis for the `(2m-2)`-loops
        have hIH := StochDom.sqrt_of (hY0 _) (fun N _ _ => pow_nonneg (ha0 N).le _)
          (ih k (by omega) hk0)
        have h1 := StochDom.mul (fun N u ω => Real.sqrt_nonneg _)
          (fun N _ _ => mul_nonneg (mul_nonneg hC (ha0 N).le) (hNr N)) hT1 hIH
        have h2 := StochDom.mul (fun N u ω => Real.sqrt_nonneg (Y (2 * (k + 1)) N u ω))
          (fun N _ _ => mul_nonneg (mul_nonneg (mul_nonneg hC (ha0 N).le) (hNr N))
            (Real.sqrt_nonneg _)) h1
          (StochDom.refl (fun N u ω => Real.sqrt_nonneg (Y (2 * (k + 1)) N u ω)))
        refine (StochDom.of_le_left (fun N u ω => ?_) h2).mono_right_eventually ?_
        · simp only [Pi.mul_apply]
          have hodd' := hodd k hk0 N u ω
          rw [show 2 * k + 2 = 2 * (k + 1) by ring] at hodd'
          have hy : Y (2 * k + 1) N u ω
              ≤ Real.sqrt (Y (2 * k) N u ω) * Real.sqrt (Y (2 * (k + 1)) N u ω) := by
            rw [← Real.sqrt_mul (hY0 _ N u ω)]
            exact Real.le_sqrt_of_sq_le hodd'
          have hk := mul_nonneg (hK0 N) (Real.rpow_nonneg (hT0 p N u ω) r)
          calc K N * (Y (2 * k + 1) N u ω * T p N u ω ^ r)
              = (K N * T p N u ω ^ r) * Y (2 * k + 1) N u ω := by ring
            _ ≤ (K N * T p N u ω ^ r)
                * (Real.sqrt (Y (2 * k) N u ω) * Real.sqrt (Y (2 * (k + 1)) N u ω)) :=
                mul_le_mul_of_nonneg_left hy hk
            _ = _ := by ring
        · filter_upwards with N u ω
          simp only [Pi.mul_apply]
          have e : Real.sqrt (A N * Y (2 * (k + 1)) N u ω)
              = a N * Real.sqrt (a N ^ (2 * k - 1)) * Real.sqrt (Y (2 * (k + 1)) N u ω) := by
            simp only [hA]
            rw [show 2 * k + 1 = 2 + (2 * k - 1) by omega, pow_add,
              Real.sqrt_mul (mul_nonneg (pow_nonneg (ha0 N).le _) (pow_nonneg (ha0 N).le _)),
              Real.sqrt_mul (pow_nonneg (ha0 N).le _), Real.sqrt_sq (ha0 N).le]
          rw [e]
          have : 0 ≤ 2 * C * A N * (N : ℝ) ^ r :=
            mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC) (hA0 N)) (hNr N)
          nlinarith [this]
    -- (6.13): assemble
    have hsum : ∀ N u ω, Y (2 * (k + 1)) N u ω ≤ ((k : ℝ) + 2) * ((T (2 * (k + 1)) N u ω
        + ∑ l ∈ Finset.range k,
          K N * (Y (2 * l + 1) N u ω * T (p * (2 * (k + 1 - l) - 1)) N u ω ^ r))
        + K N * (Y (2 * k + 1) N u ω * T p N u ω ^ r)) := by
      intro N u ω
      have h := hrec (k + 1) (by omega) p hp N u ω
      rw [Finset.sum_range_succ, show k + 1 - k = 1 by omega,
        show p * (2 * 1 - 1) = p by ring, ← hr] at h
      refine h.trans (le_of_eq ?_)
      rw [mul_add (K N), Finset.mul_sum]
      push_cast
      ring
    have hR := StochDom.det_mul_of (f := fun _ => (k : ℝ) + 2) (fun _ => by positivity)
      (fun N u ω => add_nonneg (add_nonneg (hT0 _ N u ω) (Finset.sum_nonneg fun l _ =>
        mul_nonneg (hK0 N) (mul_nonneg (hY0 _ N u ω) (Real.rpow_nonneg (hT0 _ N u ω) r))))
        (mul_nonneg (hK0 N) (mul_nonneg (hY0 _ N u ω) (Real.rpow_nonneg (hT0 _ N u ω) r))))
      ((hR1.add hR2).add hR3)
    set D1 : ℝ := ((k : ℝ) + 2) * (1 + ((k : ℝ) + 2) * C) with hD1
    set D2 : ℝ := ((k : ℝ) + 2) * C with hD2
    set D : ℝ := (D1 + D2 + 1) ^ 2 with hD
    have hD1_0 : 0 ≤ D1 := mul_nonneg (by positivity) (by nlinarith)
    have hD2_0 : 0 ≤ D2 := mul_nonneg (by positivity) hC
    have hD1D : D1 ≤ D := by nlinarith
    have hD2D : D2 ^ 2 ≤ D := by nlinarith
    have hD0 : 0 ≤ D := sq_nonneg _
    have hstep : StochDom P (Y (2 * (k + 1))) (fun N u ω =>
        D * ((N : ℝ) ^ r * (N : ℝ) ^ r * A N)
          + Real.sqrt (D * ((N : ℝ) ^ r * (N : ℝ) ^ r * A N) * Y (2 * (k + 1)) N u ω)) := by
      refine (StochDom.of_le_left (fun N u ω => hsum N u ω) hR).mono_right_eventually ?_
      filter_upwards [hev] with N hN u ω
      simp only [Pi.add_apply, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      set x := (N : ℝ) ^ r
      set y := Y (2 * (k + 1)) N u ω
      have hx1 : 1 ≤ x := hN.1
      have hy : 0 ≤ y := hY0 _ N u ω
      have hAy : 0 ≤ A N * y := mul_nonneg (hA0 N) hy
      have p1 : ((k : ℝ) + 2) * (A N * x + k * (C * A N * x) + 2 * C * A N * x)
          ≤ D * (x * x * A N) := by
        have e : ((k : ℝ) + 2) * (A N * x + k * (C * A N * x) + 2 * C * A N * x)
            = D1 * (A N * x) := by rw [hD1]; ring
        rw [e]
        have hAx : 0 ≤ A N * x := mul_nonneg (hA0 N) (by linarith)
        calc D1 * (A N * x) ≤ D * (A N * x) := mul_le_mul_of_nonneg_right hD1D hAx
          _ ≤ D * (A N * x * x) := mul_le_mul_of_nonneg_left
              (le_mul_of_one_le_right hAx hx1) hD0
          _ = D * (x * x * A N) := by ring
      have p2 : ((k : ℝ) + 2) * (C * x * Real.sqrt (A N * y))
          ≤ Real.sqrt (D * (x * x * A N) * y) := by
        refine Real.le_sqrt_of_sq_le ?_
        have e : (((k : ℝ) + 2) * (C * x * Real.sqrt (A N * y))) ^ 2
            = D2 ^ 2 * (x ^ 2 * (A N * y)) := by
          rw [show ((k : ℝ) + 2) * (C * x * Real.sqrt (A N * y))
            = D2 * x * Real.sqrt (A N * y) by rw [hD2]; ring, mul_pow, mul_pow,
            Real.sq_sqrt hAy]
          ring
        rw [e]
        calc D2 ^ 2 * (x ^ 2 * (A N * y)) ≤ D * (x ^ 2 * (A N * y)) :=
              mul_le_mul_of_nonneg_right hD2D (mul_nonneg (sq_nonneg _) hAy)
          _ = D * (x * x * A N) * y := by ring
      calc ((k : ℝ) + 2) * (A N * x + k * (C * A N * x)
            + (2 * C * A N * x + C * x * Real.sqrt (A N * y)))
          = ((k : ℝ) + 2) * (A N * x + k * (C * A N * x) + 2 * C * A N * x)
            + ((k : ℝ) + 2) * (C * x * Real.sqrt (A N * y)) := by ring
        _ ≤ _ := add_le_add p1 p2
    have hZ0 : ∀ N (u : U N) (ω : Ω), 0 ≤ (N : ℝ) ^ r * (N : ℝ) ^ r * A N :=
      fun N _ _ => mul_nonneg (mul_nonneg (hNr N) (hNr N)) (hA0 N)
    have hZ := StochDom.of_le_add_sqrt_mul (hY0 _) (fun N u ω => mul_nonneg hD0 (hZ0 N u ω))
      hstep
    have hfin : StochDom P (fun N (_ : U N) (_ : Ω) => D * ((N : ℝ) ^ r * (N : ℝ) ^ r * A N))
        (fun N _ _ => (N : ℝ) ^ δ * A N) := by
      refine (StochDom.const_mul_left hD0 hZ0 (StochDom.refl hZ0)).mono_right_eventually ?_
      filter_upwards [eventually_ge_atTop 1] with N hN1 u ω
      have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
      rw [← Real.rpow_add' (Nat.cast_nonneg N) (by positivity)]
      exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hN1' hrδ) (hA0 N)
    exact hZ.trans hfin
  intro n hn
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · exact hE m (by omega)
  · rw [show 2 * m + 1 - 1 = 2 * m by omega]
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · exact hY1'
    · refine StochDom.odd_of_even (fun N => (ha0 N).le) hY0 hm0 (hodd m hm0) (hE m hm0) ?_
      have := hE (m + 1) (by omega)
      rwa [show 2 * (m + 1) = 2 * m + 2 by ring, show 2 * m + 2 - 1 = 2 * m + 1 by omega]
        at this

end Recursion

section BaseCase

variable {L W : ℕ} [NeZero L] [NeZero W] {H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ}
  {z : ℂ}

/-- `|⟨M E_b⟩| ≤ K` if every diagonal entry of `M` has modulus `≤ K`. -/
theorem norm_trace_mul_Eblk_le_of_diag (M : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ)
    (b : ZMod L) {K : ℝ} (hM : ∀ p, ‖M p p‖ ≤ K) : ‖trace (M * Eblk L W b)‖ ≤ K := by
  rw [Eblk_eq_diagonal_bw, trace]
  simp only [diag_apply, mul_diagonal]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ p, ‖M p p * ((bw b p : ℝ) : ℂ)‖ ≤ ∑ p, K * bw b p := by
        refine Finset.sum_le_sum fun p _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (bw_nonneg b p)]
        exact mul_le_mul_of_nonneg_right (hM p) (bw_nonneg b p)
    _ = K := by rw [← Finset.mul_sum, sum_bw, mul_one]

/-- **The base case (5.6)**: if `|G_{ii}| ≤ K` for all `i` (in particular on
`Ω = {‖G‖_max ≤ 2}` with `K = 2`), every loop of length `1` is bounded by `K`. -/
theorem loopMax_one_le (hH : H.IsHermitian) {K : ℝ} (hK : ∀ i, ‖green H z i i‖ ≤ K) :
    loopMax L W H z 1 ≤ K := by
  refine loopMax_le fun I hσ ha => ?_
  obtain ⟨σ, a⟩ := I
  obtain ⟨s, rfl⟩ := List.length_eq_one_iff.mp hσ
  obtain ⟨b, rfl⟩ := List.length_eq_one_iff.mp ha
  have e : gloop L W H z ⟨[s], [b]⟩ = trace (Gsig H z s * Eblk L W b) := by
    simp [gloop, gloopProd_cons, gloopProd_nil]
  rw [e]
  refine norm_trace_mul_Eblk_le_of_diag _ b fun p => ?_
  cases s
  · have h := Gsig_conjTranspose hH z true
    simp only [Bool.not_true] at h
    rw [← h, conjTranspose_apply, norm_star]
    exact hK p
  · exact hK p

end BaseCase

section Lemma51

open Filter MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- A `≺`-bound for all loops of length `n` (parameter `(σ, a) ∈ LoopData`) is a `≺`-bound for
their maximum `loopMax`. -/
theorem stochDom_loopMax_of_loopData {Hf : ∀ N, Ω → Matrix (B.Idx N) (B.Idx N) ℂ} {zf : ℕ → ℂ}
    {n : ℕ} {ζ : ℕ → ℝ}
    (h : StochDom B.P (fun N (u : LoopData (B.L N) n) ω =>
      ‖gloop (B.L N) (B.W N) (Hf N ω) (zf N) u.idx‖) (fun N _ _ => ζ N)) :
    StochDom B.P (fun N (_ : Unit) ω => loopMax (B.L N) (B.W N) (Hf N ω) (zf N) n)
      (fun N _ _ => ζ N) := by
  intro τ hτ D hD
  filter_upwards [h τ hτ D hD] with N hN
  refine (measure_mono ?_).trans hN
  rintro ω ⟨_, hu⟩
  by_contra hno
  simp only [badSet, Set.mem_ofPred_eq, not_exists, not_lt] at hno
  exact absurd hu (not_lt.2 (ciSup_le fun x => hno x))

/-- **(6.1) as a hypothesis** (the random layer is not formalized).  With
`G̃_{t₁} = (H_{t₂} - z̃_{t₁})⁻¹`, `z̃_{t₁} = (t₂/t₁)^{1/2} z_{t₁}`, the paper uses
`L̃_{t₁} ∼ (t₁/t₂)^{n/2} L_{t₁}` in distribution (jointly in `(σ, a)`), which follows from
`H_{t₂} ∼ (t₂/t₁)^{1/2} H_{t₁}`.  Since `(t₁/t₂)^{n/2} ≤ 1`, every bound
`max_{σ,a} |L_{t₁,σ,a}| ≤ N^τ ζ` with deterministic `ζ` transfers to the loops of `G̃`; that
transfer of `≺`-bounds is what is recorded here (the only form in which §6 uses (6.1)). -/
structure LoopScaling (X : Sample B) (E : ℝ) (t₁ t₂ : ℕ → ℝ) : Prop where
  transfer : ∀ n : ℕ, 1 ≤ n → ∀ ζ : ℕ → ℝ,
    StochDom B.P (fun N (u : LoopData (B.L N) n) ω => ‖X.Lval E N (t₁ N) ω u.idx‖)
      (fun N _ _ => ζ N) →
    StochDom B.P (fun N (u : LoopData (B.L N) n) ω =>
      ‖gloop (B.L N) (B.W N) (X.H N (t₂ N) ω) (ztTilde E (t₁ N) (t₂ N)) u.idx‖)
      (fun N _ _ => ζ N)

/-- **The event (5.6)** `Ω = {‖G_t‖_max ≤ 2}`. -/
def Sample.gmaxEvent (X : Sample B) (E : ℝ) (t : ℕ → ℝ) (N : ℕ) : Set Ω :=
  {ω | ∀ i j, ‖X.G E N (t N) ω i j‖ ≤ 2}

/-- **Lemma 5.1 (continuity estimate on loops).**  Let `c ≤ t₁ ≤ t₂ < 1`, `|E| ≤ 2 - κ`.
Assume (5.5): for every `n ≥ 1`, `max_{σ,a} |L_{t₁,σ,a}| ≺ (Wℓ₁η₁)^{-n+1}`, and the scaling
(6.1) (`LoopScaling`).  Then for every `n ≥ 1`, with `Ω` the event (5.6),
\[ 1_Ω \max_{σ,a}|\mathcal L_{t_2,σ,a}| \prec (Wℓ_1η_2)^{-n+1}. \] -/
theorem lemma_5_1 (X : Sample B) {E κ c : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) (hc : 0 < c)
    {t₁ t₂ : ℕ → ℝ} (h₁ : ∀ N, c ≤ t₁ N) (h₁₂ : ∀ N, t₁ N ≤ t₂ N) (h₂ : ∀ N, t₂ N < 1)
    (hS : LoopScaling X E t₁ t₂)
    (h55 : ∀ n : ℕ, 1 ≤ n → StochDom B.P
      (fun N (u : LoopData (B.L N) n) ω => ‖X.Lval E N (t₁ N) ω u.idx‖)
      (fun N _ _ => (B.scale E N (t₁ N))⁻¹ ^ (n - 1))) :
    ∀ n : ℕ, 1 ≤ n → StochDom B.P
      (fun N (u : LoopData (B.L N) n) ω =>
        (X.gmaxEvent E t₂ N).indicator (fun ω => ‖X.Lval E N (t₂ N) ω u.idx‖) ω)
      (fun N _ _ => ((B.W N : ℝ) * B.ell N (t₁ N) * etaT E (t₂ N))⁻¹ ^ (n - 1)) := by
  have hE2 : |E| < 2 := by linarith
  obtain ⟨C, hC0, hC⟩ := ztTilde_arith hc hκ
  -- the deterministic quantities
  set a : ℕ → ℝ := fun N => ((B.W N : ℝ) * B.ell N (t₁ N) * etaT E (t₂ N))⁻¹ with ha_def
  set a1 : ℕ → ℝ := fun N => (B.scale E N (t₁ N))⁻¹ with ha1_def
  set zz : ℕ → ℂ := fun N => zt E (t₂ N)
  set zw : ℕ → ℂ := fun N => ztTilde E (t₁ N) (t₂ N)
  set K : ℕ → ℝ := fun N => ‖zz N - zw N‖ ^ 2 * ((zz N).im * (zw N).im)⁻¹ with hK_def
  have ht₁0 : ∀ N, 0 < t₁ N := fun N => hc.trans_le (h₁ N)
  have ht₁1 : ∀ N, t₁ N < 1 := fun N => (h₁₂ N).trans_lt (h₂ N)
  have hW : ∀ N, (0 : ℝ) < B.W N := fun N => by exact_mod_cast B.W_pos N
  have hℓ : ∀ N, 1 ≤ B.ell N (t₁ N) := fun N =>
    one_le_ellHat (B.L N) (B.three_le_L N) (ht₁0 N) (ht₁1 N)
  have hη1 : ∀ N, 0 < etaT E (t₁ N) := fun N => etaT_pos hE2 (ht₁1 N)
  have hη2 : ∀ N, 0 < etaT E (t₂ N) := fun N => etaT_pos hE2 (h₂ N)
  have hmIm : 0 ≤ (mE E).im := (mE_im_pos hE2).le
  have hη12 : ∀ N, etaT E (t₂ N) ≤ etaT E (t₁ N) := fun N => by
    unfold etaT
    exact mul_le_mul_of_nonneg_right (by linarith [h₁₂ N]) hmIm
  have hzz : ∀ N, (zz N).im = etaT E (t₂ N) := fun N => (etaT_eq_zt_im E (t₂ N)).symm
  have harith := fun N => hC E (t₁ N) (t₂ N) (h₁ N) (h₁₂ N) (h₂ N).le hE
  have hzw : ∀ N, etaT E (t₁ N) ≤ (zw N).im := fun N => (harith N).2.2.2.1
  have hzw0 : ∀ N, 0 < (zw N).im := fun N => (hη1 N).trans_le (hzw N)
  have hA2 : ∀ N, 0 < (B.W N : ℝ) * B.ell N (t₁ N) * etaT E (t₂ N) := fun N =>
    mul_pos (mul_pos (hW N) (by linarith [hℓ N])) (hη2 N)
  have ha1 : ∀ N, 0 < a1 N := fun N => inv_pos.mpr (B.scale_pos hE2 N (ht₁0 N) (ht₁1 N))
  have ha1a : ∀ N, a1 N ≤ a N := fun N => by
    simp only [ha1_def, ha_def, Band.scale]
    refine inv_anti₀ (hA2 N) ?_
    have hℓ0 : (0 : ℝ) < B.ell N (t₁ N) := by linarith [hℓ N]
    exact mul_le_mul_of_nonneg_left (hη12 N) (mul_pos (hW N) hℓ0).le
  have hK0 : ∀ N, 0 ≤ K N := fun N =>
    mul_nonneg (sq_nonneg _) (inv_nonneg.mpr (mul_nonneg (by rw [hzz]; exact (hη2 N).le)
      (hzw0 N).le))
  have hK : ∀ N, K N * a1 N ≤ C * a N := by
    intro N
    have hsq := (harith N).2.1
    set x := ‖zz N - zw N‖ ^ 2
    have hx : x ≤ C * etaT E (t₁ N) * (zw N).im := by
      calc x ≤ C * etaT E (t₁ N) ^ 2 := hsq
        _ = C * etaT E (t₁ N) * etaT E (t₁ N) := by ring
        _ ≤ C * etaT E (t₁ N) * (zw N).im :=
            mul_le_mul_of_nonneg_left (hzw N) (mul_nonneg hC0.le (hη1 N).le)
    simp only [hK_def, ha1_def, ha_def, Band.scale, hzz]
    have hq := hzw0 N
    have hℓ0 : 0 < B.ell N (t₁ N) := by linarith [hℓ N]
    have hden : 0 < etaT E (t₂ N) * (zw N).im := mul_pos (hη2 N) hq
    calc x * (etaT E (t₂ N) * (zw N).im)⁻¹ * ((B.W N : ℝ) * B.ell N (t₁ N) * etaT E (t₁ N))⁻¹
        ≤ (C * etaT E (t₁ N) * (zw N).im) * (etaT E (t₂ N) * (zw N).im)⁻¹
          * ((B.W N : ℝ) * B.ell N (t₁ N) * etaT E (t₁ N))⁻¹ := by
          have hA1 : 0 < (B.W N : ℝ) * B.ell N (t₁ N) * etaT E (t₁ N) :=
            mul_pos (mul_pos (hW N) hℓ0) (hη1 N)
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hx
            (inv_nonneg.mpr hden.le)) (inv_nonneg.mpr hA1.le)
      _ = C * ((B.W N : ℝ) * B.ell N (t₁ N) * etaT E (t₂ N))⁻¹ := by
          have := hη1 N; have := hη2 N; have := hW N
          field_simp
  have hNev : ∀ᶠ N : ℕ in atTop, (a1 N)⁻¹ ≤ N := by
    filter_upwards [B.dim] with N hdim
    simp only [ha1_def, inv_inv, Band.scale]
    have hWL : (B.W N : ℝ) * B.L N ≤ N := by exact_mod_cast hdim.1
    have hℓL : B.ell N (t₁ N) ≤ B.L N := min_le_right _ _
    have hη1' : etaT E (t₁ N) ≤ 1 := by
      unfold etaT
      have hm1 : (mE E).im ≤ 1 := (le_abs_self _).trans ((Complex.abs_im_le_norm _).trans
        (norm_mE (by linarith)).le)
      have : 1 - t₁ N ≤ 1 := by linarith [ht₁0 N]
      nlinarith [ht₁1 N]
    calc (B.W N : ℝ) * B.ell N (t₁ N) * etaT E (t₁ N) ≤ (B.W N : ℝ) * B.L N * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hℓL (hW N).le) hη1' (hη1 N).le
            (mul_nonneg (hW N).le (Nat.cast_nonneg _))
      _ ≤ N := by rw [mul_one]; exact hWL
  -- the random families: `Y_n = 1_Ω max|L_{t₂}^{(n)}|` and `T_n = max|L̃^{(n)}|`
  set Ωs := X.gmaxEvent E t₂ with hΩs
  set Y : ℕ → ∀ N, (fun _ => Unit) N → Ω → ℝ := fun n N _ ω =>
    (Ωs N).indicator (fun ω => loopMax (B.L N) (B.W N) (X.H N (t₂ N) ω) (zz N) n) ω with hY
  set T : ℕ → ∀ N, (fun _ => Unit) N → Ω → ℝ := fun n N _ ω =>
    loopMax (B.L N) (B.W N) (X.H N (t₂ N) ω) (zw N) n with hT
  have hY0 : ∀ n N u ω, 0 ≤ Y n N u ω := fun n N u ω =>
    Set.indicator_nonneg (fun ω _ => loopMax_nonneg _) ω
  have hT0 : ∀ n N u ω, 0 ≤ T n N u ω := fun n N u ω => loopMax_nonneg _
  have hTd : ∀ n, 1 ≤ n → StochDom B.P (T n) (fun N _ _ => a1 N ^ (n - 1)) := fun n hn =>
    stochDom_loopMax_of_loopData (hS.transfer n hn _ (h55 n hn))
  have hY1 : ∀ N u ω, Y 1 N u ω ≤ 2 := by
    intro N u ω
    by_cases hω : ω ∈ Ωs N
    · simp only [hY, Set.indicator_of_mem hω]
      exact loopMax_one_le (X.hermitian N (t₂ N) ω) (fun i => hω i i)
    · simp only [hY, Set.indicator_of_notMem hω]
      norm_num
  have hodd : ∀ l, 1 ≤ l → ∀ N u ω,
      Y (2 * l + 1) N u ω ^ 2 ≤ Y (2 * l) N u ω * Y (2 * l + 2) N u ω := by
    intro l hl N u ω
    by_cases hω : ω ∈ Ωs N
    · simp only [hY, Set.indicator_of_mem hω]
      exact loopMax_odd_sq_le (X.hermitian N (t₂ N) ω) hl
    · simp [hY, Set.indicator_of_notMem hω]
  have hrec : ∀ m, 1 ≤ m → ∀ p, 1 ≤ p → ∀ N u ω, Y (2 * m) N u ω ≤ (m + 1 : ℝ) *
      (T (2 * m) N u ω + K N * ∑ l ∈ Finset.range m,
        Y (2 * l + 1) N u ω * T (p * (2 * (m - l) - 1)) N u ω ^ (1 / (p : ℝ))) := by
    intro m hm p hp N u ω
    by_cases hω : ω ∈ Ωs N
    · simp only [hY, hT, Set.indicator_of_mem hω]
      have hz : 0 < (zz N).im := by rw [hzz]; exact hη2 N
      refine (loopMax_two_mul_le_tilde (X.hermitian N (t₂ N) ω) hz (hzw0 N) hm hp).trans
        (le_of_eq ?_)
      simp only [hK_def]
      ring
    · simp only [hY, hT, Set.indicator_of_notMem hω, zero_mul, Finset.sum_const_zero,
        mul_zero, add_zero]
      exact mul_nonneg (by positivity) (loopMax_nonneg _)
  have hmain := StochDom.continuity_recursion (P := B.P) hY0 hT0 ha1 ha1a hK0 hC0.le hK hNev
    hTd hY1 hodd hrec
  intro n hn
  have h1 := (hmain n hn).precomp_param (fun N (_ : LoopData (B.L N) n) => ())
  refine StochDom.of_le_left (fun N u ω => ?_) h1
  exact Set.indicator_le_indicator
    (norm_gloop_le_loopMax u.idx (by simp [LoopData.idx]) (by simp [LoopData.idx]))

/-- **Lemma 5.1, (5.7) in the paper's second form**:
`1_Ω max_{σ,a}|L_{t₂,σ,a}| ≺ (ℓ₂/ℓ₁)^{n-1} (Wℓ₂η₂)^{-n+1}`. -/
theorem lemma_5_1' (X : Sample B) {E κ c : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) (hc : 0 < c)
    {t₁ t₂ : ℕ → ℝ} (h₁ : ∀ N, c ≤ t₁ N) (h₁₂ : ∀ N, t₁ N ≤ t₂ N) (h₂ : ∀ N, t₂ N < 1)
    (hS : LoopScaling X E t₁ t₂)
    (h55 : ∀ n : ℕ, 1 ≤ n → StochDom B.P
      (fun N (u : LoopData (B.L N) n) ω => ‖X.Lval E N (t₁ N) ω u.idx‖)
      (fun N _ _ => (B.scale E N (t₁ N))⁻¹ ^ (n - 1))) :
    ∀ n : ℕ, 1 ≤ n → StochDom B.P
      (fun N (u : LoopData (B.L N) n) ω =>
        (X.gmaxEvent E t₂ N).indicator (fun ω => ‖X.Lval E N (t₂ N) ω u.idx‖) ω)
      (fun N _ _ => (B.ell N (t₂ N) / B.ell N (t₁ N)) ^ (n - 1)
        * (B.scale E N (t₂ N))⁻¹ ^ (n - 1)) := by
  intro n hn
  have h := lemma_5_1 X hκ hE hc h₁ h₁₂ h₂ hS h55 n hn
  have hE2 : |E| < 2 := by linarith
  convert h using 3 with N u ω
  have ht₂0 : 0 < t₂ N := (hc.trans_le (h₁ N)).trans_le (h₁₂ N)
  have hℓ1 : 0 < B.ell N (t₁ N) := lt_of_lt_of_le zero_lt_one
    (one_le_ellHat (B.L N) (B.three_le_L N) (hc.trans_le (h₁ N)) ((h₁₂ N).trans_lt (h₂ N)))
  have hℓ2 : 0 < B.ell N (t₂ N) := lt_of_lt_of_le zero_lt_one
    (one_le_ellHat (B.L N) (B.three_le_L N) ht₂0 (h₂ N))
  have hW : (0 : ℝ) < B.W N := by exact_mod_cast B.W_pos N
  have hη : 0 < etaT E (t₂ N) := etaT_pos hE2 (h₂ N)
  rw [← mul_pow, Band.scale]
  field_simp

end Lemma51

end RBM
