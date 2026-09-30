/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Defs.Block
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# The block band model

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, Section 2.1 and (2.5).

The matrix has `L` blocks of size `W`, so it is `N × N` with `N = W L`, indexed by
`ZMod N`.  The `a`-th block is `I_a = {aW, aW + 1, …, aW + W - 1}` for `a ∈ ZMod L`.
The paper defines the variance profile by
`S_{ij} = (3W)⁻¹ ∑_a 1(i ∈ I_a) 1(j ∈ I_a ∪ I_{a+1} ∪ I_{a-1})`
and observes that `S = S^(B) ⊗ S_W` with `(S_W)_{αβ} = W⁻¹`.

We work with the block/offset index `ZMod L × Fin W`, on which `S` is literally the
Kronecker product `RBM.Svar = S^(B) ⊗ₖ S_W`; the paper's index `i ∈ ZMod N` corresponds to
`(⌊i/W⌋, i mod W)`.

## Main definitions

* `RBM.SW`, `RBM.Svar`  : `S_W` and `S = S^(B) ⊗ S_W`
* `RBM.Eblk`            : the normalized block projection `E_a` of (2.5)

## Main results

* `RBM.sum_Eblk`        : `∑_a E_a = W⁻¹ I`, used in Step 1 of Lemma 3.6
* `RBM.Eblk_conjTranspose`, `RBM.Eblk_mul_Eblk`
-/

namespace RBM

open Matrix Finset
open scoped Kronecker

section Kronecker

variable (L W : ℕ)

/-- The `W × W` matrix `S_W` with all entries `W⁻¹`. -/
noncomputable def SW : Matrix (Fin W) (Fin W) ℂ := Matrix.of fun _ _ => (W : ℂ)⁻¹

/-- The variance profile `S = S^(B) ⊗ S_W` of Section 2.1, on the block/offset index. -/
noncomputable def Svar : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ := SB L ⊗ₖ SW W

theorem Svar_apply (a b : ZMod L) (α β : Fin W) :
    Svar L W (a, α) (b, β) = SB L a b * (W : ℂ)⁻¹ := rfl

/-- The normalized block projection `E_a` of (2.5): `(E_a)_{ij} = δ_{ij} W⁻¹ 1(i ∈ I_a)`. -/
noncomputable def Eblk (a : ZMod L) : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ :=
  diagonal fun p => if p.1 = a then (W : ℂ)⁻¹ else 0

/-- `∑_a E_a = W⁻¹ I`. -/
theorem sum_Eblk [NeZero L] : ∑ a, Eblk L W a = (W : ℂ)⁻¹ • (1 : Matrix _ _ ℂ) := by
  ext p q
  simp only [Matrix.sum_apply, Eblk, diagonal_apply, Matrix.smul_apply, one_apply, smul_eq_mul]
  split_ifs with h
  · simp [Finset.sum_ite_eq]
  · simp

theorem Eblk_conjTranspose (a : ZMod L) : (Eblk L W a)ᴴ = Eblk L W a := by
  rw [Eblk, diagonal_conjTranspose]
  congr 1
  funext p
  simp only [Pi.star_apply]
  split_ifs <;> simp

theorem Eblk_mul_Eblk [NeZero L] (a b : ZMod L) :
    Eblk L W a * Eblk L W b = if a = b then (W : ℂ)⁻¹ • Eblk L W a else 0 := by
  rw [Eblk, Eblk, diagonal_mul_diagonal]
  split_ifs with hab
  · subst hab
    rw [← diagonal_smul]
    congr 1
    funext p
    simp only [Pi.smul_apply, smul_eq_mul]
    split_ifs <;> ring
  · rw [← diagonal_zero]
    congr 1
    funext p
    split_ifs with h1 h2
    · exact absurd (h1.symm.trans h2) hab
    · ring
    · ring
    · ring

end Kronecker

section Paper

variable (L W : ℕ) [NeZero L] [NeZero W]

omit [NeZero L] [NeZero W] in
theorem sub_mem_sbSupport_iff (x y : ZMod L) :
    x - y ∈ sbSupport L ↔ y = x ∨ y = x + 1 ∨ y = x - 1 := by
  simp only [sbSupport, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (h | h | h)
    · left; linear_combination -h
    · right; right; linear_combination -h
    · right; left; linear_combination -h
  · rintro (h | h | h)
    · left; linear_combination -h
    · right; right; linear_combination -h
    · right; left; linear_combination -h

end Paper

end RBM
