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
Kronecker product `RBM.Svar = S^(B) ⊗ₖ S_W`.  The literal definitions on `ZMod N`
(`RBM.Spaper`, `RBM.Epaper`) are also given, and `RBM.Spaper_eq`, `RBM.Epaper_eq`
identify them with `Svar`, `Eblk` through the bijection `i ↦ (⌊i/W⌋, i mod W)`.

## Main definitions

* `RBM.SW`, `RBM.Svar`  : `S_W` and `S = S^(B) ⊗ S_W`
* `RBM.Eblk`            : the normalized block projection `E_a` of (2.5)
* `RBM.Iblk`, `RBM.Spaper`, `RBM.Epaper` : the paper's literal definitions on `ZMod N`
* `RBM.splitEquiv`      : `ZMod N ≃ ZMod L × Fin W`, `i ↦ (⌊i/W⌋, i mod W)`

## Main results

* `RBM.sum_Svar_row`    : `∑_j S_{ij} = 1`
* `RBM.Svar_transpose`  : `S = Sᵀ`
* `RBM.sum_Eblk`        : `∑_a E_a = W⁻¹ I`, used in Step 1 of Lemma 3.6
* `RBM.Eblk_conjTranspose`, `RBM.Eblk_mul_Eblk`
* `RBM.mem_Iblk`, `RBM.Spaper_eq`, `RBM.Epaper_eq` : agreement with the paper's formulas
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

theorem SW_transpose : (SW W)ᵀ = SW W := rfl

theorem sum_SW_row [NeZero W] (α : Fin W) : ∑ β, SW W α β = 1 := by
  simp only [SW, Matrix.of_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne W))

/-- `S` is symmetric. -/
theorem Svar_transpose : (Svar L W)ᵀ = Svar L W := by
  ext ⟨a, α⟩ ⟨b, β⟩
  rw [transpose_apply, Svar_apply, Svar_apply,
    show SB L b a = SB L a b from congrFun (congrFun (SB_transpose L) a) b]

/-- Each row of `S` sums to `1`. -/
theorem sum_Svar_row [NeZero L] [NeZero W] (hL : 3 ≤ L) (i : ZMod L × Fin W) :
    ∑ j, Svar L W i j = 1 := by
  obtain ⟨a, α⟩ := i
  rw [Fintype.sum_prod_type]
  simp only [Svar, kronecker_apply, ← Finset.mul_sum, sum_SW_row, mul_one]
  exact sum_SB_row L hL a

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

/-- The block containing `i ∈ ZMod N`: `⌊i/W⌋`. -/
def blk (i : ZMod (W * L)) : ZMod L := ((i.val / W : ℕ) : ZMod L)

/-- The position of `i` inside its block: `i mod W`. -/
def ofs (i : ZMod (W * L)) : Fin W := ⟨i.val % W, Nat.mod_lt _ (NeZero.pos W)⟩

/-- `i ↦ (⌊i/W⌋, i mod W)`. -/
def split (i : ZMod (W * L)) : ZMod L × Fin W := (blk L W i, ofs L W i)

theorem blk_val (i : ZMod (W * L)) : (blk L W i).val = i.val / W :=
  ZMod.val_natCast_of_lt (Nat.div_lt_of_lt_mul (ZMod.val_lt i))

/-- The `a`-th block `I_a = {aW, aW + 1, …, aW + W - 1} ⊆ ZMod N`. -/
def Iblk (a : ZMod L) : Finset (ZMod (W * L)) :=
  (Finset.range W).image fun α => ((a.val * W + α : ℕ) : ZMod (W * L))

theorem mem_Iblk (a : ZMod L) (i : ZMod (W * L)) : i ∈ Iblk L W a ↔ blk L W i = a := by
  have hW : 0 < W := NeZero.pos W
  rw [Iblk, Finset.mem_image]
  constructor
  · rintro ⟨α, hα, rfl⟩
    rw [Finset.mem_range] at hα
    have hlt : a.val * W + α < W * L := by
      have := ZMod.val_lt a
      nlinarith
    rw [blk, ZMod.val_natCast_of_lt hlt, mul_comm, Nat.mul_add_div hW,
      Nat.div_eq_of_lt hα, add_zero, ZMod.natCast_zmod_val]
  · intro h
    refine ⟨i.val % W, Finset.mem_range.mpr (Nat.mod_lt _ hW), ?_⟩
    rw [← h, blk_val, Nat.div_add_mod', ZMod.natCast_zmod_val]

/-- The variance profile exactly as written in Section 2.1:
`S_{ij} = (3W)⁻¹ ∑_a 1(i ∈ I_a) 1(j ∈ I_a ∪ I_{a+1} ∪ I_{a-1})`. -/
noncomputable def Spaper (i j : ZMod (W * L)) : ℂ :=
  (3 * W : ℂ)⁻¹ * ∑ a : ZMod L, (if i ∈ Iblk L W a then 1 else 0) *
    (if j ∈ Iblk L W a ∪ Iblk L W (a + 1) ∪ Iblk L W (a - 1) then 1 else 0)

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

/-- The paper's `S` is the Kronecker product `S^(B) ⊗ S_W` under `i ↦ (⌊i/W⌋, i mod W)`. -/
theorem Spaper_eq (i j : ZMod (W * L)) :
    Spaper L W i j = Svar L W (split L W i) (split L W j) := by
  classical
  have hmem : ∀ a, (j ∈ Iblk L W a ∪ Iblk L W (a + 1) ∪ Iblk L W (a - 1))
      ↔ (blk L W j = a ∨ blk L W j = a + 1 ∨ blk L W j = a - 1) := by
    intro a
    simp only [Finset.mem_union, mem_Iblk, or_assoc]
  simp only [Spaper, mem_Iblk, hmem, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, ↓reduceIte, split, Svar_apply, SB_apply, sbKernel,
    sub_mem_sbSupport_iff]
  have hW : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne W)
  split_ifs
  · field_simp
  · ring

theorem split_injective : Function.Injective (split L W) := by
  intro i j h
  simp only [split, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have hb : i.val / W = j.val / W := by rw [← blk_val, ← blk_val, h1]
  have ho : i.val % W = j.val % W := congrArg Fin.val h2
  apply ZMod.val_injective
  rw [← Nat.div_add_mod' i.val W, ← Nat.div_add_mod' j.val W, hb, ho]

theorem split_bijective : Function.Bijective (split L W) := by
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨split_injective L W, ?_⟩
  rw [ZMod.card, Fintype.card_prod, ZMod.card, Fintype.card_fin, mul_comm]

/-- `ZMod N ≃ ZMod L × Fin W`, `i ↦ (⌊i/W⌋, i mod W)`. -/
noncomputable def splitEquiv : ZMod (W * L) ≃ ZMod L × Fin W :=
  Equiv.ofBijective _ (split_bijective L W)

/-- As matrices: `S = (S^(B) ⊗ S_W)` reindexed along `splitEquiv`. -/
theorem Spaper_eq_submatrix :
    Matrix.of (Spaper L W) = (Svar L W).submatrix (split L W) (split L W) := by
  ext i j
  exact Spaper_eq L W i j

/-- The block projection exactly as written in (2.5):
`(E_a)_{ij} = δ_{ij} W⁻¹ 1(i ∈ I_a)`. -/
noncomputable def Epaper (a : ZMod L) : Matrix (ZMod (W * L)) (ZMod (W * L)) ℂ :=
  Matrix.of fun i j => if i = j then (W : ℂ)⁻¹ * (if i ∈ Iblk L W a then 1 else 0) else 0

theorem Epaper_eq (a : ZMod L) (i j : ZMod (W * L)) :
    Epaper L W a i j = Eblk L W a (split L W i) (split L W j) := by
  simp only [Epaper, Matrix.of_apply, Eblk, diagonal_apply, (split_injective L W).eq_iff,
    mem_Iblk]
  simp only [split]
  by_cases h : i = j
  · subst h
    split_ifs <;> simp [*]
  · simp [h]

end Paper

end RBM
