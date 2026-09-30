/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.OpNorm
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Order.Interval.Finset.Fin

/-!
# Courant–Fischer and Weyl's inequality for `eigenvalues₀`

Formalization of the linear-algebra half of the GUE-comparison route to Theorem 2.6 Step 1:
the perturbation (Weyl) bound

`|hA.eigenvalues₀ i - hB.eigenvalues₀ i| ≤ ‖A - B‖ ≤ √(∑_{ij} |A_ij - B_ij|²)`

for Hermitian matrices `A, B : Matrix n n ℂ`, where `hA.eigenvalues₀ : Fin (Fintype.card n) → ℝ`
is Mathlib's `Matrix.IsHermitian.eigenvalues₀` (`Analysis/Matrix/Spectrum.lean`, sorted in
decreasing order) and `‖A - B‖` is the `Matrix.Norms.L2Operator` operator norm used throughout
`RBM1D/Gauss/OpNorm.lean`.

## Route

There is no Courant–Fischer min-max theorem in Mathlib, so the one-sided form actually needed is
built from scratch: for a symmetric operator `T` on a finite-dimensional inner product space and
an index `i`, any subspace `W` of dimension `≥ m - i` meets the span of the top `i+1`
eigenvectors of `T` in a nonzero vector, and on the span of the top `i+1` eigenvectors the
Rayleigh quotient of `T` is `≥` the `i`-th eigenvalue (dually, on the span of the bottom `m - i`
eigenvectors it is `≤`).  Applying this with `T = toEuclideanLin A` and `W` the bottom
`(m - i)`-dimensional eigenspace of `B` gives `λ_i(A) ≤ λ_i(B) + ‖A - B‖`; swapping `A, B` gives
the reverse inequality, and `RBM.Gauss.l2_opNorm_sq_le_frobSq` (`Gauss/OpNorm.lean`) bounds
`‖A - B‖` by the Frobenius norm.

## Main results

* `RBM.Gauss.eigenvalues₀_abs_sub_le` — the Weyl inequality.

## What is private

Everything else (`EigenWeyl.*`) is the Courant–Fischer scaffolding; these
helpers are file-stem prefixed and not part of the public interface.
-/

namespace RBM.Gauss

open Matrix
open scoped Matrix.Norms.L2Operator

/-! ### Abstract Courant–Fischer scaffolding for a symmetric operator -/

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  {T : E →ₗ[ℂ] E}

/-- The real part of `⟪T v, v⟫` decomposes over the eigenbasis of a symmetric operator. -/
private lemma EigenWeyl.reInner_eq_sum {m : ℕ} (hT : T.IsSymmetric)
    (hn : Module.finrank ℂ E = m) (v : E) :
    RCLike.re (inner ℂ (T v) v) =
      ∑ j : Fin m, hT.eigenvalues hn j * ‖(hT.eigenvectorBasis hn).repr v j‖ ^ 2 := by
  have hb := (hT.eigenvectorBasis hn).repr.inner_map_map (T v) v
  rw [← hb, PiLp.inner_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hT.eigenvectorBasis_apply_self_apply hn v j, RCLike.inner_apply', map_mul (starRingEnd ℂ),
    RCLike.conj_ofReal, mul_assoc, RCLike.conj_mul, RCLike.re_ofReal_mul, RCLike.re_ofReal_pow]

/-- Parseval: `‖v‖²` decomposes over the eigenbasis of a symmetric operator. -/
private lemma EigenWeyl.norm_sq_eq_sum {m : ℕ} (hT : T.IsSymmetric)
    (hn : Module.finrank ℂ E = m) (v : E) :
    ‖v‖ ^ 2 = ∑ j : Fin m, ‖(hT.eigenvectorBasis hn).repr v j‖ ^ 2 := by
  rw [← (hT.eigenvectorBasis hn).repr.norm_map v, EuclideanSpace.norm_sq_eq]

/-- A vector in the span of a finite sub-family of the eigenbasis has zero coordinates outside
that sub-family. -/
private lemma EigenWeyl.repr_eq_zero_of_not_mem {m : ℕ} (hT : T.IsSymmetric)
    (hn : Module.finrank ℂ E = m) {s : Finset (Fin m)} {x : E}
    (hx : x ∈ Submodule.span ℂ ((hT.eigenvectorBasis hn) '' (s : Set (Fin m))))
    {j : Fin m} (hj : j ∉ s) :
    (hT.eigenvectorBasis hn).repr x j = 0 := by
  classical
  obtain ⟨c, hc⟩ := (Submodule.mem_span_image_finset_iff_exists_fun' (R := ℂ)).mp hx
  rw [← hc, map_sum]
  simp only [map_smul]
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  refine Finset.sum_eq_zero fun k hk => ?_
  have hkj : j ≠ k := fun h => hj (h ▸ hk)
  rw [(hT.eigenvectorBasis hn).repr_self k]
  simp [hkj]

/-- The dimension of the span of the eigenvectors indexed by a finite set of indices. -/
private lemma EigenWeyl.finrank_span_eigenvectorBasis {m : ℕ} (hT : T.IsSymmetric)
    (hn : Module.finrank ℂ E = m) (s : Finset (Fin m)) :
    Module.finrank ℂ (Submodule.span ℂ ((hT.eigenvectorBasis hn) '' (s : Set (Fin m))))
      = s.card := by
  classical
  have hli : LinearIndependent ℂ ((hT.eigenvectorBasis hn) ∘ ((↑) : s → Fin m)) :=
    (hT.eigenvectorBasis hn).orthonormal.linearIndependent.comp
      ((↑) : s → Fin m) Subtype.val_injective
  have hrange : Set.range ((hT.eigenvectorBasis hn) ∘ ((↑) : s → Fin m))
      = (hT.eigenvectorBasis hn) '' (s : Set (Fin m)) := by
    ext y
    constructor
    · rintro ⟨k, rfl⟩; exact ⟨(k : Fin m), k.2, rfl⟩
    · rintro ⟨k, hk, rfl⟩; exact ⟨⟨k, hk⟩, rfl⟩
  have hfr := finrank_span_eq_card hli
  rw [hrange] at hfr
  rw [hfr, Fintype.card_coe]

/-- On the span of the top `i + 1` eigenvectors, the Rayleigh quotient of a symmetric operator
is at least the `i`-th eigenvalue. -/
private lemma EigenWeyl.rayleigh_ge_of_mem_Iic {m : ℕ} (hT : T.IsSymmetric)
    (hn : Module.finrank ℂ E = m) (i : Fin m) {x : E}
    (hx : x ∈ Submodule.span ℂ ((hT.eigenvectorBasis hn) '' (Finset.Iic i : Set (Fin m)))) :
    hT.eigenvalues hn i * ‖x‖ ^ 2 ≤ RCLike.re (inner ℂ (T x) x) := by
  rw [EigenWeyl.reInner_eq_sum hT hn x, EigenWeyl.norm_sq_eq_sum hT hn x, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  by_cases hj : j ∈ (Finset.Iic i)
  · exact mul_le_mul_of_nonneg_right (hT.eigenvalues_antitone hn (Finset.mem_Iic.mp hj))
      (sq_nonneg _)
  · rw [EigenWeyl.repr_eq_zero_of_not_mem hT hn hx hj]; simp

/-- On the span of the bottom `m - i` eigenvectors, the Rayleigh quotient of a symmetric operator
is at most the `i`-th eigenvalue. -/
private lemma EigenWeyl.rayleigh_le_of_mem_Ici {m : ℕ} (hT : T.IsSymmetric)
    (hn : Module.finrank ℂ E = m) (i : Fin m) {x : E}
    (hx : x ∈ Submodule.span ℂ ((hT.eigenvectorBasis hn) '' (Finset.Ici i : Set (Fin m)))) :
    RCLike.re (inner ℂ (T x) x) ≤ hT.eigenvalues hn i * ‖x‖ ^ 2 := by
  rw [EigenWeyl.reInner_eq_sum hT hn x, EigenWeyl.norm_sq_eq_sum hT hn x, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  by_cases hj : j ∈ (Finset.Ici i)
  · exact mul_le_mul_of_nonneg_right (hT.eigenvalues_antitone hn (Finset.mem_Ici.mp hj))
      (sq_nonneg _)
  · rw [EigenWeyl.repr_eq_zero_of_not_mem hT hn hx hj]; simp

/-- The Courant–Fischer half we need: any subspace of dimension `≥ m - i` contains a nonzero
vector on which the Rayleigh quotient of `T` is `≥` the `i`-th eigenvalue. -/
private lemma EigenWeyl.exists_ge_rayleigh_of_finrank_ge {m : ℕ} (hT : T.IsSymmetric)
    (hn : Module.finrank ℂ E = m) (i : Fin m) {W : Submodule ℂ E}
    (hW : m - i.1 ≤ Module.finrank ℂ W) :
    ∃ x ∈ W, x ≠ 0 ∧ hT.eigenvalues hn i * ‖x‖ ^ 2 ≤ RCLike.re (inner ℂ (T x) x) := by
  classical
  have hUfr : Module.finrank ℂ
      (Submodule.span ℂ ((hT.eigenvectorBasis hn) '' (Finset.Iic i : Set (Fin m)))) = i.1 + 1 := by
    rw [EigenWeyl.finrank_span_eigenvectorBasis hT hn (Finset.Iic i), Fin.card_Iic]
  have him : i.1 < m := i.2
  have hcard : m - i.1 + (i.1 + 1) = m + 1 := by omega
  have hne : W ⊓ Submodule.span ℂ ((hT.eigenvectorBasis hn) '' (Finset.Iic i : Set (Fin m)))
      ≠ ⊥ := by
    intro hbot
    have hfin := Submodule.finrank_sup_add_finrank_inf_eq W
      (Submodule.span ℂ ((hT.eigenvectorBasis hn) '' (Finset.Iic i : Set (Fin m))))
    rw [hbot, finrank_bot, add_zero] at hfin
    have hsup_le : Module.finrank ℂ
        (↥(W ⊔ Submodule.span ℂ ((hT.eigenvectorBasis hn) '' (Finset.Iic i : Set (Fin m)))))
        ≤ Module.finrank ℂ E := Submodule.finrank_le _
    rw [hn] at hsup_le
    omega
  obtain ⟨x, hxmem, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hxW : x ∈ W := (Submodule.mem_inf.mp hxmem).1
  have hxU : x ∈ Submodule.span ℂ ((hT.eigenvectorBasis hn) '' (Finset.Iic i : Set (Fin m))) :=
    (Submodule.mem_inf.mp hxmem).2
  exact ⟨x, hxW, hx0, EigenWeyl.rayleigh_ge_of_mem_Iic hT hn i hxU⟩

end Abstract

/-! ### Specialization to Hermitian matrices -/

section Matrices

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The symmetric linear map underlying a Hermitian matrix. -/
private theorem EigenWeyl.sym {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (Matrix.toEuclideanLin A).IsSymmetric :=
  isSymmetric_toEuclideanLin_iff.mpr hA

/-- `eigenvalues₀` is literally the abstract `LinearMap.IsSymmetric.eigenvalues` of
`toEuclideanLin A`; this is the bridge between the abstract scaffolding above and Mathlib's
`Matrix.IsHermitian.eigenvalues₀`. -/
private lemma EigenWeyl.eigenvalues₀_eq {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    hA.eigenvalues₀ = (EigenWeyl.sym hA).eigenvalues finrank_euclideanSpace := rfl

/-- The operator norm bounds the norm of `toEuclideanLin C` applied to a unit-normalized
vector. -/
private lemma EigenWeyl.norm_toEuclideanLin_apply_le (C : Matrix n n ℂ)
    (x : EuclideanSpace ℂ n) : ‖Matrix.toEuclideanLin C x‖ ≤ ‖C‖ * ‖x‖ := by
  have hx : (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) C) x = Matrix.toEuclideanLin C x := by
    change (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) C :
      EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n) x = Matrix.toEuclideanLin C x
    rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
  have h := (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) C).le_opNorm x
  rw [hx, Matrix.l2_opNorm_toEuclideanCLM] at h
  exact h

/-- One side of Weyl's inequality: `λ_i(A) ≤ λ_i(B) + ‖A - B‖`. -/
private lemma EigenWeyl.eigenvalues₀_le_add_opNorm {A B : Matrix n n ℂ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (i : Fin (Fintype.card n)) :
    hA.eigenvalues₀ i ≤ hB.eigenvalues₀ i + ‖A - B‖ := by
  classical
  have hWdim : Fintype.card n - i.1 ≤ Module.finrank ℂ
      (Submodule.span ℂ (((EigenWeyl.sym hB).eigenvectorBasis finrank_euclideanSpace) ''
        (Finset.Ici i : Set (Fin (Fintype.card n))))) := by
    rw [EigenWeyl.finrank_span_eigenvectorBasis (EigenWeyl.sym hB) finrank_euclideanSpace
      (Finset.Ici i), Fin.card_Ici]
  obtain ⟨x, hxW, hx0, hxrayleigh⟩ :=
    EigenWeyl.exists_ge_rayleigh_of_finrank_ge (EigenWeyl.sym hA) finrank_euclideanSpace i hWdim
  have hBle := EigenWeyl.rayleigh_le_of_mem_Ici (EigenWeyl.sym hB) finrank_euclideanSpace i hxW
  have hsplit : (inner ℂ (Matrix.toEuclideanLin A x) x : ℂ) =
      inner ℂ (Matrix.toEuclideanLin B x) x
        + inner ℂ (Matrix.toEuclideanLin A x - Matrix.toEuclideanLin B x) x := by
    have hEq : Matrix.toEuclideanLin A x
        = Matrix.toEuclideanLin B x + (Matrix.toEuclideanLin A x - Matrix.toEuclideanLin B x) := by
      abel
    nth_rewrite 1 [hEq]
    rw [inner_add_left]
  have hCterm : RCLike.re
      (inner ℂ (Matrix.toEuclideanLin A x - Matrix.toEuclideanLin B x) x)
      ≤ ‖A - B‖ * ‖x‖ ^ 2 := by
    have hAB : Matrix.toEuclideanLin A x - Matrix.toEuclideanLin B x
        = Matrix.toEuclideanLin (A - B) x := by
      rw [map_sub, LinearMap.sub_apply]
    calc RCLike.re (inner ℂ (Matrix.toEuclideanLin A x - Matrix.toEuclideanLin B x) x)
        ≤ ‖(inner ℂ (Matrix.toEuclideanLin A x - Matrix.toEuclideanLin B x) x : ℂ)‖ :=
          RCLike.re_le_norm _
      _ = ‖(inner ℂ (Matrix.toEuclideanLin (A - B) x) x : ℂ)‖ := by rw [hAB]
      _ ≤ ‖Matrix.toEuclideanLin (A - B) x‖ * ‖x‖ := norm_inner_le_norm _ _
      _ ≤ (‖A - B‖ * ‖x‖) * ‖x‖ := by
          gcongr
          exact EigenWeyl.norm_toEuclideanLin_apply_le (A - B) x
      _ = ‖A - B‖ * ‖x‖ ^ 2 := by ring
  have hCbound : RCLike.re (inner ℂ (Matrix.toEuclideanLin A x) x)
      ≤ RCLike.re (inner ℂ (Matrix.toEuclideanLin B x) x) + ‖A - B‖ * ‖x‖ ^ 2 := by
    rw [hsplit, map_add]
    linarith [hCterm]
  have hxpos : 0 < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.mpr hx0) 2
  have hchain : (EigenWeyl.sym hA).eigenvalues finrank_euclideanSpace i * ‖x‖ ^ 2 ≤
      ((EigenWeyl.sym hB).eigenvalues finrank_euclideanSpace i + ‖A - B‖) * ‖x‖ ^ 2 := by
    rw [add_mul]
    linarith [hxrayleigh, hBle, hCbound]
  rw [EigenWeyl.eigenvalues₀_eq hA, EigenWeyl.eigenvalues₀_eq hB]
  exact le_of_mul_le_mul_right hchain hxpos

/-- **Weyl's perturbation inequality** for `Matrix.IsHermitian.eigenvalues₀`, together with the
Frobenius-norm bound on the operator norm (`RBM.Gauss.l2_opNorm_sq_le_frobSq`). -/
theorem eigenvalues₀_abs_sub_le {n : Type*} [Fintype n] [DecidableEq n] {A B : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (i : Fin (Fintype.card n)) :
    |hA.eigenvalues₀ i - hB.eigenvalues₀ i| ≤ Real.sqrt (∑ a, ∑ b, ‖(A - B) a b‖ ^ 2) := by
  have h1 : hA.eigenvalues₀ i ≤ hB.eigenvalues₀ i + ‖A - B‖ :=
    EigenWeyl.eigenvalues₀_le_add_opNorm hA hB i
  have h2 : hB.eigenvalues₀ i ≤ hA.eigenvalues₀ i + ‖B - A‖ :=
    EigenWeyl.eigenvalues₀_le_add_opNorm hB hA i
  have hnormBA : ‖B - A‖ = ‖A - B‖ := by rw [← neg_sub]; exact norm_neg _
  rw [hnormBA] at h2
  have habs : |hA.eigenvalues₀ i - hB.eigenvalues₀ i| ≤ ‖A - B‖ :=
    abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
  have hfrob : ‖A - B‖ ^ 2 ≤ frobSq (A - B) := l2_opNorm_sq_le_frobSq (A - B)
  have hle : ‖A - B‖ ≤ Real.sqrt (frobSq (A - B)) := Real.le_sqrt_of_sq_le hfrob
  calc |hA.eigenvalues₀ i - hB.eigenvalues₀ i|
      ≤ ‖A - B‖ := habs
    _ ≤ Real.sqrt (frobSq (A - B)) := hle
    _ = Real.sqrt (∑ a, ∑ b, ‖(A - B) a b‖ ^ 2) := by rw [frobSq]

end Matrices

/-! ### A nondegenerate example: `A ≠ B` with a strict eigenvalue change -/

section Example

end Example

end RBM.Gauss
