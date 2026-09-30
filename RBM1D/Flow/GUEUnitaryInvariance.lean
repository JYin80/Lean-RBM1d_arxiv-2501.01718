/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Flow.EigenMeasurable
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Independence.InfinitePi

/-!
# GUE unitary invariance

The standard complex GUE law `gueMeasure d N` (`OUMarginalGaussian.lean`)
is invariant under conjugation by any fixed unitary matrix (`RBM.Gauss.gueMeasure_map_conj`).

## Route

At fixed `N`, only the real coordinates `⟨N, i, j, b⟩` with `idxKey i < idxKey j` (both booleans)
or `i = j` (only `b = true`) are read by `Xmat d N`.  These form the finite slot type `GUESlot d N`
below.  The real-linear reconstruction map `GUEReconSlot` (slot values → Hermitian matrix) and
its left inverse `GUEExtractSlot` (Hermitian matrix → slot values) identify `Xmat d N` with the
composite `GUEReconSlot ∘ (restriction of ω to slots)`.  The key algebraic fact
(`GUEMainIdentity`) is `∑ q, (GUEExtractSlot d N K q)² / GUEWt d N q.1 = M · Tr(K²)` for
Hermitian `K`, summed over the slots `q` (`GUEWt` the slot's Gaussian variance, `M` the matrix
size): the left side is a weighted Euclidean norm of the real
coordinates, the right side (via `Matrix.trace_mul_comm` and the unitary relations
`U * Uᴴ = 1 = Uᴴ * U`) is invariant under `K ↦ Uᴴ K U`.  Composing `GUEReconSlot`,
`GUEExtractSlot` and the fixed
conjugation `ψ_U` therefore gives a **linear isometry equivalence** of `EuclideanSpace ℝ (GUESlot
d N)` (after standardizing each slot by the square root of its variance), to which
`ProbabilityTheory.stdGaussian_map` applies directly.  Matching the actual coordinate measure
`gueMeasure d N` restricted to the slots with this standardized picture
(`ProbabilityTheory.map_pi_eq_stdGaussian`, `MeasureTheory.Measure.pi_map_pi`,
`gaussianReal_map_const_mul`) gives `gueMeasure_map_conj`.
-/

open MeasureTheory ProbabilityTheory Filter Matrix Topology WithLp
open scoped ComplexConjugate NNReal ENNReal

namespace RBM.Gauss

variable (d : Dims)

/-! ### The real-coordinate slot type at fixed matrix size `N` -/

/-- Which triples `(i, j, b)` carry a real coordinate read by `Xmat d N`: either
`idxKey i < idxKey j` (either boolean), or `i = j` (only `b = true`).  File-local. -/
private def GUESlotPred (d : Dims) (N : ℕ) (q : d.Idx N × d.Idx N × Bool) : Prop :=
  idxKey d N q.1 < idxKey d N q.2.1 ∨ (q.1 = q.2.1 ∧ q.2.2 = true)

private instance instDecidablePredGUESlotPred (d : Dims) (N : ℕ) :
    DecidablePred (GUESlotPred d N) := fun q => by unfold GUESlotPred; infer_instance

/-- The finite index set of real coordinates read by `Xmat d N`. -/
private def GUESlot (d : Dims) (N : ℕ) : Type :=
  {q : d.Idx N × d.Idx N × Bool // GUESlotPred d N q}

private instance instFintypeGUESlot (d : Dims) (N : ℕ) : Fintype (GUESlot d N) :=
  Subtype.fintype _

/-! ### The Gaussian variance of a slot (total function, matches `gueCoordVar`) -/

private noncomputable def GUEWt (d : Dims) (N : ℕ) (q : d.Idx N × d.Idx N × Bool) : ℝ :=
  (gueCoordVar d N ⟨N, q⟩ : ℝ)

private theorem GUEWt_pos (d : Dims) (N : ℕ) (q : d.Idx N × d.Idx N × Bool) :
    0 < GUEWt d N q := by
  have hM : (0 : ℝ) < (ouMatrixSize d N : ℝ) := by exact_mod_cast ouMatrixSize_pos d N
  unfold GUEWt
  rcases q with ⟨i, j, b⟩
  by_cases h : i = j
  · subst h
    rw [gueCoordVar_diag d N i b]
    positivity
  · rw [gueCoordVar_offDiag d N i j b h]
    positivity

/-! ### Reconstruction and extraction (total functions on all triples) -/

/-- Rebuild a Hermitian matrix from a total assignment of real values to triples
`(i, j, b)`, using only the values at slots (mirrors `RBM.Gauss.Xentry`). -/
private noncomputable def GUERe (d : Dims) (N : ℕ) (x : d.Idx N × d.Idx N × Bool → ℝ) :
    Matrix (d.Idx N) (d.Idx N) ℂ :=
  Matrix.of fun i j =>
    if idxKey d N i < idxKey d N j then
      (x (i, j, true) : ℂ) + Complex.I * (x (i, j, false) : ℂ)
    else if idxKey d N j < idxKey d N i then
      (x (j, i, true) : ℂ) - Complex.I * (x (j, i, false) : ℂ)
    else
      (x (i, i, true) : ℂ)

/-- Extract the real value of a matrix entry at a triple `(i, j, b)` (mirrors the inverse of
`Xentry`; well-behaved only at slots, but total). -/
private noncomputable def GUEEx (d : Dims) (N : ℕ) (K : Matrix (d.Idx N) (d.Idx N) ℂ) :
    d.Idx N × d.Idx N × Bool → ℝ :=
  fun q => if q.1 = q.2.1 ∨ q.2.2 = true then (K q.1 q.2.1).re else (K q.1 q.2.1).im

private theorem GUERe_apply_lt (d : Dims) (N : ℕ) (x : d.Idx N × d.Idx N × Bool → ℝ)
    {i j : d.Idx N} (h : idxKey d N i < idxKey d N j) :
    GUERe d N x i j = (x (i, j, true) : ℂ) + Complex.I * (x (i, j, false) : ℂ) := by
  simp only [GUERe, Matrix.of_apply, if_pos h]

private theorem GUERe_apply_gt (d : Dims) (N : ℕ) (x : d.Idx N × d.Idx N × Bool → ℝ)
    {i j : d.Idx N} (h : idxKey d N j < idxKey d N i) :
    GUERe d N x i j = (x (j, i, true) : ℂ) - Complex.I * (x (j, i, false) : ℂ) := by
  have hne : ¬ idxKey d N i < idxKey d N j := asymm h
  simp only [GUERe, Matrix.of_apply, if_neg hne, if_pos h]

private theorem GUERe_apply_diag (d : Dims) (N : ℕ) (x : d.Idx N × d.Idx N × Bool → ℝ)
    (i : d.Idx N) :
    GUERe d N x i i = (x (i, i, true) : ℂ) := by
  simp only [GUERe, Matrix.of_apply, if_neg (lt_irrefl (idxKey d N i))]

/-- **Hermitian-ness of `GUERe`**, for any real coordinate assignment. -/
private theorem GUERe_isHermitian (d : Dims) (N : ℕ) (x : d.Idx N × d.Idx N × Bool → ℝ) :
    (GUERe d N x).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  have hstar : ∀ z : ℂ, star z = (starRingEnd ℂ) z := fun _ => rfl
  rcases idxKey_lt_or_eq_or_lt d N i j with h | h | h
  · rw [GUERe_apply_lt d N x h, GUERe_apply_gt d N x h, hstar]
    apply Complex.ext <;> simp [Complex.conj_re, Complex.conj_im]
  · subst h
    rw [GUERe_apply_diag d N x i, hstar]
    apply Complex.ext <;> simp [Complex.conj_re, Complex.conj_im]
  · rw [GUERe_apply_gt d N x h, GUERe_apply_lt d N x h, hstar]
    apply Complex.ext <;> simp [Complex.conj_re, Complex.conj_im]

/-- **Extraction after reconstruction recovers a slot's value.** -/
private theorem GUEEx_GUERe (d : Dims) (N : ℕ) (x : d.Idx N × d.Idx N × Bool → ℝ)
    {q : d.Idx N × d.Idx N × Bool} (hq : GUESlotPred d N q) :
    GUEEx d N (GUERe d N x) q = x q := by
  rcases q with ⟨i, j, b⟩
  rcases hq with h | ⟨hij, hb⟩
  · have hne : i ≠ j := fun he => absurd h (he ▸ lt_irrefl _)
    have hval : GUERe d N x i j = (x (i, j, true) : ℂ) + Complex.I * (x (i, j, false) : ℂ) :=
      GUERe_apply_lt d N x h
    cases b
    · have e : GUEEx d N (GUERe d N x) (i, j, false) = (GUERe d N x i j).im := by
        simp [GUEEx, hne]
      rw [e, hval]
      simp
    · have e : GUEEx d N (GUERe d N x) (i, j, true) = (GUERe d N x i j).re := by
        simp [GUEEx]
      rw [e, hval]
      simp
  · dsimp only at hij hb
    subst hij
    subst hb
    have e : GUEEx d N (GUERe d N x) (i, i, true) = (GUERe d N x i i).re := by
      simp [GUEEx]
    rw [e, GUERe_apply_diag d N x i]
    simp

/-- **Reconstruction after extraction recovers a Hermitian matrix.** -/
private theorem GUERe_GUEEx (d : Dims) (N : ℕ) {K : Matrix (d.Idx N) (d.Idx N) ℂ}
    (hK : K.IsHermitian) : GUERe d N (GUEEx d N K) = K := by
  ext i j
  rcases idxKey_lt_or_eq_or_lt d N i j with h | h | h
  · have hne : i ≠ j := fun he => absurd h (he ▸ lt_irrefl _)
    rw [GUERe_apply_lt d N (GUEEx d N K) h]
    have e1 : GUEEx d N K (i, j, true) = (K i j).re := by simp [GUEEx]
    have e2 : GUEEx d N K (i, j, false) = (K i j).im := by simp [GUEEx, hne]
    rw [e1, e2, mul_comm]
    exact Complex.re_add_im (K i j)
  · subst h
    rw [GUERe_apply_diag d N (GUEEx d N K) i]
    have e : GUEEx d N K (i, i, true) = (K i i).re := by simp [GUEEx]
    rw [e]
    have him : (K i i).im = 0 := by
      have hKii : star (K i i) = K i i := hK.apply i i
      have hcong := congrArg Complex.im hKii
      simp only [show ∀ z : ℂ, star z = (starRingEnd ℂ) z from fun _ => rfl,
        Complex.conj_im] at hcong
      linarith
    apply Complex.ext
    · simp
    · simp [him]
  · have hne : i ≠ j := fun he => absurd h (he ▸ lt_irrefl _)
    rw [GUERe_apply_gt d N (GUEEx d N K) h]
    have e1 : GUEEx d N K (j, i, true) = (K j i).re := by simp [GUEEx]
    have e2 : GUEEx d N K (j, i, false) = (K j i).im := by simp [GUEEx, Ne.symm hne]
    rw [e1, e2]
    have hKij : star (K i j) = K j i := hK.apply j i
    have hcong : K i j = star (K j i) := by rw [← hKij, star_star]
    rw [hcong]
    apply Complex.ext <;> simp

/-! ### `GUERe`, `GUEEx` are real-linear -/

private theorem GUE_real_smul (c : ℝ) (z : ℂ) : c • z = (c : ℂ) * z := rfl

private theorem GUERe_add (d : Dims) (N : ℕ) (x y : d.Idx N × d.Idx N × Bool → ℝ) :
    GUERe d N (x + y) = GUERe d N x + GUERe d N y := by
  ext i j
  rcases idxKey_lt_or_eq_or_lt d N i j with h | h | h
  · rw [Matrix.add_apply, GUERe_apply_lt d N x h, GUERe_apply_lt d N y h,
      GUERe_apply_lt d N (x + y) h]
    simp only [Pi.add_apply, Complex.ofReal_add]
    ring
  · subst h
    rw [Matrix.add_apply, GUERe_apply_diag d N x i, GUERe_apply_diag d N y i,
      GUERe_apply_diag d N (x + y) i]
    simp only [Pi.add_apply, Complex.ofReal_add]
  · rw [Matrix.add_apply, GUERe_apply_gt d N x h, GUERe_apply_gt d N y h,
      GUERe_apply_gt d N (x + y) h]
    simp only [Pi.add_apply, Complex.ofReal_add]
    ring

private theorem GUERe_smul (d : Dims) (N : ℕ) (c : ℝ) (x : d.Idx N × d.Idx N × Bool → ℝ) :
    GUERe d N (c • x) = c • GUERe d N x := by
  ext i j
  rcases idxKey_lt_or_eq_or_lt d N i j with h | h | h
  · rw [Matrix.smul_apply, GUERe_apply_lt d N x h, GUERe_apply_lt d N (c • x) h]
    simp only [Pi.smul_apply, smul_eq_mul, GUE_real_smul, Complex.ofReal_mul]
    ring
  · subst h
    rw [Matrix.smul_apply, GUERe_apply_diag d N x i, GUERe_apply_diag d N (c • x) i]
    simp only [Pi.smul_apply, smul_eq_mul, GUE_real_smul, Complex.ofReal_mul]
  · rw [Matrix.smul_apply, GUERe_apply_gt d N x h, GUERe_apply_gt d N (c • x) h]
    simp only [Pi.smul_apply, smul_eq_mul, GUE_real_smul, Complex.ofReal_mul]
    ring

private theorem GUEEx_add (d : Dims) (N : ℕ) (K L : Matrix (d.Idx N) (d.Idx N) ℂ) :
    GUEEx d N (K + L) = GUEEx d N K + GUEEx d N L := by
  funext q
  unfold GUEEx
  by_cases hc : q.1 = q.2.1 ∨ q.2.2 = true
  · simp [hc]
  · simp [hc]

private theorem GUEEx_smul (d : Dims) (N : ℕ) (c : ℝ) (K : Matrix (d.Idx N) (d.Idx N) ℂ) :
    GUEEx d N (c • K) = c • GUEEx d N K := by
  funext q
  unfold GUEEx
  by_cases hc : q.1 = q.2.1 ∨ q.2.2 = true
  · simp only [hc, if_true, Matrix.smul_apply, Complex.smul_re, smul_eq_mul, Pi.smul_apply,
      if_pos]
  · simp only [hc, if_false, Matrix.smul_apply, Complex.smul_im, smul_eq_mul, Pi.smul_apply,
      if_neg, not_false_eq_true]

/-! ### The fixed conjugation `H ↦ Uᴴ H U`, and its interaction with `GUERe`/`GUEEx` -/

private noncomputable def GUEConj (d : Dims) (N : ℕ) (U : Matrix (d.Idx N) (d.Idx N) ℂ)
    (H : Matrix (d.Idx N) (d.Idx N) ℂ) : Matrix (d.Idx N) (d.Idx N) ℂ :=
  Uᴴ * H * U

private theorem GUEConj_isHermitian (d : Dims) (N : ℕ) (U : Matrix (d.Idx N) (d.Idx N) ℂ)
    {H : Matrix (d.Idx N) (d.Idx N) ℂ} (hH : H.IsHermitian) :
    (GUEConj d N U H).IsHermitian := by
  show (Uᴴ * H * U)ᴴ = Uᴴ * H * U
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hH,
    Matrix.mul_assoc]

private theorem GUEConj_add (d : Dims) (N : ℕ) (U : Matrix (d.Idx N) (d.Idx N) ℂ)
    (H1 H2 : Matrix (d.Idx N) (d.Idx N) ℂ) :
    GUEConj d N U (H1 + H2) = GUEConj d N U H1 + GUEConj d N U H2 := by
  show Uᴴ * (H1 + H2) * U = Uᴴ * H1 * U + Uᴴ * H2 * U
  rw [Matrix.mul_add, Matrix.add_mul]

private theorem GUEConj_smul (d : Dims) (N : ℕ) (U : Matrix (d.Idx N) (d.Idx N) ℂ) (c : ℝ)
    (H : Matrix (d.Idx N) (d.Idx N) ℂ) :
    GUEConj d N U (c • H) = c • GUEConj d N U H := by
  show Uᴴ * (c • H) * U = c • (Uᴴ * H * U)
  rw [Matrix.mul_smul, Matrix.smul_mul]

/-- `Uᴴ * (Uᴴ H U) * U`-type cancellation: conjugating by `U` then by `Uᴴ` is the identity, for
any unitary `U`. -/
private theorem GUEConj_conj_left (d : Dims) (N : ℕ) {U : Matrix (d.Idx N) (d.Idx N) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (d.Idx N) ℂ) (H : Matrix (d.Idx N) (d.Idx N) ℂ) :
    GUEConj d N Uᴴ (GUEConj d N U H) = H := by
  show Uᴴᴴ * (Uᴴ * H * U) * Uᴴ = H
  rw [Matrix.conjTranspose_conjTranspose]
  have h1 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  have h2 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  calc U * (Uᴴ * H * U) * Uᴴ = (U * Uᴴ) * H * (U * Uᴴ) := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc U Uᴴ H, ← Matrix.mul_assoc U,
          Matrix.mul_assoc]
    _ = H := by rw [h1, Matrix.one_mul, Matrix.mul_one]

private theorem GUEConj_conj_right (d : Dims) (N : ℕ) {U : Matrix (d.Idx N) (d.Idx N) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (d.Idx N) ℂ) (H : Matrix (d.Idx N) (d.Idx N) ℂ) :
    GUEConj d N U (GUEConj d N Uᴴ H) = H := by
  have hU' : Uᴴ ∈ Matrix.unitaryGroup (d.Idx N) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp hU
  have := GUEConj_conj_left d N hU' H
  rwa [Matrix.conjTranspose_conjTranspose] at this

/-! ### The algebraic core: `∑ (extraction)²/(variance) = M · Tr(K²)` and unitary invariance -/

private theorem GUE_card_idx (d : Dims) (N : ℕ) :
    Fintype.card (d.Idx N) = ouMatrixSize d N := by
  show Fintype.card (ZMod (d.L N) × Fin (d.W N)) = d.L N * d.W N
  rw [Fintype.card_prod, ZMod.card, Fintype.card_fin]

private theorem GUE_re_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    (∑ i ∈ s, f i).re = ∑ i ∈ s, (f i).re := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s' hnotmem ih =>
      rw [Finset.sum_insert hnotmem, Finset.sum_insert hnotmem, Complex.add_re, ih]

private theorem GUE_normSq_star (z : ℂ) : Complex.normSq (star z) = Complex.normSq z := by
  rw [show star z = (starRingEnd ℂ) z from rfl, Complex.normSq_conj]

/-- **Step 1 of the main identity**: `Tr(K²).re` as a double sum of `normSq`, using only that
`K` is Hermitian. -/
private theorem GUE_trace_sq_re (d : Dims) (N : ℕ) {K : Matrix (d.Idx N) (d.Idx N) ℂ}
    (hK : K.IsHermitian) :
    (Matrix.trace (K * K)).re = ∑ i, ∑ j, Complex.normSq (K i j) := by
  have htr : Matrix.trace (K * K) = ∑ i, ∑ j, K i j * K j i := by
    simp [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  rw [htr, GUE_re_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [GUE_re_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hji : K j i = star (K i j) := (hK.apply j i).symm
  have heq : K i j * K j i = ((Complex.normSq (K i j) : ℝ) : ℂ) := by
    rw [hji, show star (K i j) = (starRingEnd ℂ) (K i j) from rfl, Complex.mul_conj]
  rw [heq]
  simp

/-- **Step 2 of the main identity**: the sum of the two boolean slots at a fixed `(i, j)`. -/
private theorem GUE_bool_sum (d : Dims) (N : ℕ) {K : Matrix (d.Idx N) (d.Idx N) ℂ}
    (hK : K.IsHermitian) (i j : d.Idx N) :
    (∑ b : Bool, if GUESlotPred d N (i, j, b) then
        (GUEEx d N K (i, j, b)) ^ 2 / GUEWt d N (i, j, b) else 0) =
      if i = j then (Fintype.card (d.Idx N) : ℝ) * Complex.normSq (K i j)
      else if idxKey d N i < idxKey d N j then
        2 * (Fintype.card (d.Idx N) : ℝ) * Complex.normSq (K i j)
      else 0 := by
  have hM : (0 : ℝ) < (ouMatrixSize d N : ℝ) := by exact_mod_cast ouMatrixSize_pos d N
  have hcard : (Fintype.card (d.Idx N) : ℝ) = (ouMatrixSize d N : ℝ) := by
    exact_mod_cast GUE_card_idx d N
  rw [Fintype.sum_bool]
  by_cases hij : i = j
  · subst hij
    have hSPt : GUESlotPred d N (i, i, true) := Or.inr ⟨rfl, rfl⟩
    have hSPf : ¬ GUESlotPred d N (i, i, false) := by
      simp [GUESlotPred, lt_irrefl]
    rw [if_pos rfl, if_pos hSPt, if_neg hSPf]
    have e : GUEEx d N K (i, i, true) = (K i i).re := by simp [GUEEx]
    have hw : GUEWt d N (i, i, true) = 1 / (ouMatrixSize d N : ℝ) := gueCoordVar_diag d N i true
    rw [e, add_zero, hw, hcard]
    have him : (K i i).im = 0 := by
      have hKii : star (K i i) = K i i := hK.apply i i
      have hcong := congrArg Complex.im hKii
      simp only [show ∀ z : ℂ, star z = (starRingEnd ℂ) z from fun _ => rfl,
        Complex.conj_im] at hcong
      linarith
    rw [Complex.normSq_apply, him]
    field_simp
    ring
  · rw [if_neg hij]
    by_cases hlt : idxKey d N i < idxKey d N j
    · have hSPt : GUESlotPred d N (i, j, true) := Or.inl hlt
      have hSPf : GUESlotPred d N (i, j, false) := Or.inl hlt
      rw [if_pos hlt, if_pos hSPt, if_pos hSPf]
      have e1 : GUEEx d N K (i, j, true) = (K i j).re := by simp [GUEEx]
      have e2 : GUEEx d N K (i, j, false) = (K i j).im := by simp [GUEEx, hij]
      have hw1 : GUEWt d N (i, j, true) = 1 / (2 * (ouMatrixSize d N : ℝ)) :=
        gueCoordVar_offDiag d N i j true hij
      have hw2 : GUEWt d N (i, j, false) = 1 / (2 * (ouMatrixSize d N : ℝ)) :=
        gueCoordVar_offDiag d N i j false hij
      rw [e1, e2, hw1, hw2, hcard, Complex.normSq_apply]
      field_simp
    · have hSPt : ¬ GUESlotPred d N (i, j, true) := by
        simp [GUESlotPred, hlt, hij]
      have hSPf : ¬ GUESlotPred d N (i, j, false) := by
        simp [GUESlotPred, hlt, hij]
      rw [if_neg hlt, if_neg hSPt, if_neg hSPf]
      ring

/-- **Step 3 of the main identity**: the off-diagonal contribution is symmetric under swapping
`i` and `j` (uses `K`'s Hermitian symmetry). -/
private theorem GUE_swap_sum (d : Dims) (N : ℕ) {K : Matrix (d.Idx N) (d.Idx N) ℂ}
    (hK : K.IsHermitian) (c : ℝ) :
    ∑ i : d.Idx N, ∑ j : d.Idx N,
        (if idxKey d N j < idxKey d N i then c * Complex.normSq (K i j) else 0) =
      ∑ i : d.Idx N, ∑ j : d.Idx N,
        (if idxKey d N i < idxKey d N j then c * Complex.normSq (K i j) else 0) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  by_cases hab : idxKey d N a < idxKey d N b
  · rw [if_pos hab, if_pos hab]
    have hsymm : Complex.normSq (K b a) = Complex.normSq (K a b) := by
      have hba : K b a = star (K a b) := (hK.apply b a).symm
      rw [hba, GUE_normSq_star]
    rw [hsymm]
  · rw [if_neg hab, if_neg hab]

/-- **Main identity**: the weighted sum of squared slot values equals `M · Tr(K²).re`, for
Hermitian `K`. -/
private theorem GUEMainIdentity (d : Dims) (N : ℕ) {K : Matrix (d.Idx N) (d.Idx N) ℂ}
    (hK : K.IsHermitian) :
    ∑ q : GUESlot d N, (GUEEx d N K q.1) ^ 2 / GUEWt d N q.1 =
      (Fintype.card (d.Idx N) : ℝ) * (Matrix.trace (K * K)).re := by
  have hconv : (∑ q ∈ (Finset.univ : Finset (d.Idx N × d.Idx N × Bool)).filter (GUESlotPred d N),
      (GUEEx d N K q) ^ 2 / GUEWt d N q) =
      ∑ q : GUESlot d N, (GUEEx d N K q.1) ^ 2 / GUEWt d N q.1 :=
    Finset.sum_subtype _ (fun x => by simp) _
  rw [← hconv, Finset.sum_filter]
  have hsplit : (∑ q : d.Idx N × d.Idx N × Bool,
      if GUESlotPred d N q then (GUEEx d N K q) ^ 2 / GUEWt d N q else 0) =
      ∑ i : d.Idx N, ∑ j : d.Idx N, ∑ b : Bool,
        if GUESlotPred d N (i, j, b) then (GUEEx d N K (i, j, b)) ^ 2 / GUEWt d N (i, j, b)
        else 0 := by
    rw [Fintype.sum_prod_type (α₁ := d.Idx N) (α₂ := d.Idx N × Bool)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    exact Fintype.sum_prod_type (α₁ := d.Idx N) (α₂ := Bool)
      (f := fun y => if GUESlotPred d N (i, y) then
        (GUEEx d N K (i, y)) ^ 2 / GUEWt d N (i, y) else 0)
  rw [hsplit]
  simp_rw [GUE_bool_sum d N hK]
  rw [GUE_trace_sq_re d N hK]
  have hsep : ∀ i j : d.Idx N,
      (if i = j then (Fintype.card (d.Idx N) : ℝ) * Complex.normSq (K i j)
        else if idxKey d N i < idxKey d N j then
          2 * (Fintype.card (d.Idx N) : ℝ) * Complex.normSq (K i j) else 0) =
      (if i = j then (Fintype.card (d.Idx N) : ℝ) * Complex.normSq (K i j) else 0) +
        (if idxKey d N i < idxKey d N j then
          2 * (Fintype.card (d.Idx N) : ℝ) * Complex.normSq (K i j) else 0) := by
    intro i j
    by_cases hij : i = j
    · have hnlt : ¬ idxKey d N i < idxKey d N j := by rw [hij]; exact lt_irrefl _
      rw [if_pos hij, if_pos hij, if_neg hnlt, add_zero]
    · rw [if_neg hij, if_neg hij, zero_add]
  simp_rw [hsep, Finset.sum_add_distrib]
  have hA : ∑ i : d.Idx N, ∑ j : d.Idx N,
      (if i = j then (Fintype.card (d.Idx N) : ℝ) * Complex.normSq (K i j) else 0) =
      (Fintype.card (d.Idx N) : ℝ) * ∑ i : d.Idx N, Complex.normSq (K i i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by simp)
  have hB : ∑ i : d.Idx N, ∑ j : d.Idx N,
      (if idxKey d N i < idxKey d N j then
        2 * (Fintype.card (d.Idx N) : ℝ) * Complex.normSq (K i j) else 0) =
      2 * (Fintype.card (d.Idx N) : ℝ) * ∑ i : d.Idx N, ∑ j : d.Idx N,
        (if idxKey d N i < idxKey d N j then Complex.normSq (K i j) else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    split_ifs <;> ring
  rw [hA, hB]
  have hC : ∑ i : d.Idx N, ∑ j : d.Idx N, Complex.normSq (K i j) =
      (∑ i : d.Idx N, Complex.normSq (K i i)) +
      2 * (∑ i : d.Idx N, ∑ j : d.Idx N,
        (if idxKey d N i < idxKey d N j then Complex.normSq (K i j) else 0)) := by
    have hdecomp : ∀ i j : d.Idx N, Complex.normSq (K i j) =
        (if i = j then Complex.normSq (K i j) else 0) +
        ((if idxKey d N i < idxKey d N j then Complex.normSq (K i j) else 0) +
          (if idxKey d N j < idxKey d N i then Complex.normSq (K i j) else 0)) := by
      intro i j
      rcases idxKey_lt_or_eq_or_lt d N i j with h | h | h
      · rw [if_neg (fun he : i = j => absurd h (he ▸ lt_irrefl _)), if_pos h, if_neg (asymm h)]
        ring
      · subst h
        rw [if_pos rfl, if_neg (lt_irrefl _)]
        ring
      · rw [if_neg (fun he : i = j => absurd h (he ▸ lt_irrefl _)), if_neg (asymm h), if_pos h]
        ring
    rw [show (∑ i : d.Idx N, ∑ j : d.Idx N, Complex.normSq (K i j)) =
        ∑ i : d.Idx N, ∑ j : d.Idx N, ((if i = j then Complex.normSq (K i j) else 0) +
          ((if idxKey d N i < idxKey d N j then Complex.normSq (K i j) else 0) +
            (if idxKey d N j < idxKey d N i then Complex.normSq (K i j) else 0))) from
      Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hdecomp i j))]
    simp_rw [Finset.sum_add_distrib]
    have hdiagsum : (∑ i : d.Idx N, ∑ j : d.Idx N,
        (if i = j then Complex.normSq (K i j) else 0)) =
        ∑ i : d.Idx N, Complex.normSq (K i i) :=
      Finset.sum_congr rfl (fun i _ => by simp)
    have hswap1 : (∑ i : d.Idx N, ∑ j : d.Idx N,
        (if idxKey d N j < idxKey d N i then Complex.normSq (K i j) else 0)) =
        ∑ i : d.Idx N, ∑ j : d.Idx N,
          (if idxKey d N i < idxKey d N j then Complex.normSq (K i j) else 0) := by
      simpa using GUE_swap_sum d N hK 1
    rw [hdiagsum, hswap1]
    ring
  rw [hC]
  ring

/-! ### The subtype-indexed reconstruction/extraction, and the conjugation action on slots -/

private noncomputable def GUEExtend (d : Dims) (N : ℕ) (x : GUESlot d N → ℝ) :
    d.Idx N × d.Idx N × Bool → ℝ :=
  fun q => if h : GUESlotPred d N q then x ⟨q, h⟩ else 0

private theorem GUEExtend_add (d : Dims) (N : ℕ) (x y : GUESlot d N → ℝ) :
    GUEExtend d N (x + y) = GUEExtend d N x + GUEExtend d N y := by
  funext q
  show GUEExtend d N (x + y) q = GUEExtend d N x q + GUEExtend d N y q
  unfold GUEExtend
  by_cases h : GUESlotPred d N q
  · rw [dif_pos h, dif_pos h, dif_pos h]
    rfl
  · rw [dif_neg h, dif_neg h, dif_neg h, add_zero]

private theorem GUEExtend_smul (d : Dims) (N : ℕ) (c : ℝ) (x : GUESlot d N → ℝ) :
    GUEExtend d N (c • x) = c • GUEExtend d N x := by
  funext q
  show GUEExtend d N (c • x) q = c • GUEExtend d N x q
  unfold GUEExtend
  by_cases h : GUESlotPred d N q
  · rw [dif_pos h, dif_pos h]
    rfl
  · rw [dif_neg h, dif_neg h, smul_zero]

private noncomputable def GUEReconSlot (d : Dims) (N : ℕ) (x : GUESlot d N → ℝ) :
    Matrix (d.Idx N) (d.Idx N) ℂ :=
  GUERe d N (GUEExtend d N x)

private noncomputable def GUEExtractSlot (d : Dims) (N : ℕ) (K : Matrix (d.Idx N) (d.Idx N) ℂ) :
    GUESlot d N → ℝ :=
  fun p => GUEEx d N K p.1

private theorem GUEReconSlot_add (d : Dims) (N : ℕ) (x y : GUESlot d N → ℝ) :
    GUEReconSlot d N (x + y) = GUEReconSlot d N x + GUEReconSlot d N y := by
  unfold GUEReconSlot
  rw [GUEExtend_add, GUERe_add]

private theorem GUEReconSlot_smul (d : Dims) (N : ℕ) (c : ℝ) (x : GUESlot d N → ℝ) :
    GUEReconSlot d N (c • x) = c • GUEReconSlot d N x := by
  unfold GUEReconSlot
  rw [GUEExtend_smul, GUERe_smul]

private theorem GUEReconSlot_isHermitian (d : Dims) (N : ℕ) (x : GUESlot d N → ℝ) :
    (GUEReconSlot d N x).IsHermitian :=
  GUERe_isHermitian d N (GUEExtend d N x)

private theorem GUEExtractSlot_add (d : Dims) (N : ℕ) (K L : Matrix (d.Idx N) (d.Idx N) ℂ) :
    GUEExtractSlot d N (K + L) = GUEExtractSlot d N K + GUEExtractSlot d N L := by
  funext p
  exact congrFun (GUEEx_add d N K L) p.1

private theorem GUEExtractSlot_smul (d : Dims) (N : ℕ) (c : ℝ)
    (K : Matrix (d.Idx N) (d.Idx N) ℂ) :
    GUEExtractSlot d N (c • K) = c • GUEExtractSlot d N K := by
  funext p
  exact congrFun (GUEEx_smul d N c K) p.1

private theorem GUEExtractSlot_GUEReconSlot (d : Dims) (N : ℕ) (x : GUESlot d N → ℝ) :
    GUEExtractSlot d N (GUEReconSlot d N x) = x := by
  funext p
  show GUEEx d N (GUERe d N (GUEExtend d N x)) p.1 = x p
  rw [GUEEx_GUERe d N (GUEExtend d N x) p.2]
  unfold GUEExtend
  rw [dif_pos p.2]
  rfl

private theorem GUERe_congr_slots (d : Dims) (N : ℕ) {x y : d.Idx N × d.Idx N × Bool → ℝ}
    (h : ∀ q, GUESlotPred d N q → x q = y q) : GUERe d N x = GUERe d N y := by
  ext i j
  rcases idxKey_lt_or_eq_or_lt d N i j with hlt | heq | hgt
  · rw [GUERe_apply_lt d N x hlt, GUERe_apply_lt d N y hlt, h _ (Or.inl hlt), h _ (Or.inl hlt)]
  · subst heq
    rw [GUERe_apply_diag d N x i, GUERe_apply_diag d N y i, h _ (Or.inr ⟨rfl, rfl⟩)]
  · rw [GUERe_apply_gt d N x hgt, GUERe_apply_gt d N y hgt, h _ (Or.inl hgt), h _ (Or.inl hgt)]

private theorem GUEReconSlot_GUEExtractSlot (d : Dims) (N : ℕ)
    {K : Matrix (d.Idx N) (d.Idx N) ℂ} (hK : K.IsHermitian) :
    GUEReconSlot d N (GUEExtractSlot d N K) = K := by
  show GUERe d N (GUEExtend d N (GUEExtractSlot d N K)) = K
  rw [GUERe_congr_slots d N (x := GUEExtend d N (GUEExtractSlot d N K)) (y := GUEEx d N K)
    (fun q hq => by unfold GUEExtend GUEExtractSlot; rw [dif_pos hq])]
  exact GUERe_GUEEx d N hK

/-- The conjugation action on real slot values, `x ↦ extract (Uᴴ · reconstruct(x) · U)`. -/
private noncomputable def GUE_T (d : Dims) (N : ℕ) (U : Matrix (d.Idx N) (d.Idx N) ℂ)
    (x : GUESlot d N → ℝ) : GUESlot d N → ℝ :=
  GUEExtractSlot d N (GUEConj d N U (GUEReconSlot d N x))

private theorem GUE_T_add (d : Dims) (N : ℕ) (U : Matrix (d.Idx N) (d.Idx N) ℂ)
    (x y : GUESlot d N → ℝ) : GUE_T d N U (x + y) = GUE_T d N U x + GUE_T d N U y := by
  unfold GUE_T
  rw [GUEReconSlot_add, GUEConj_add, GUEExtractSlot_add]

private theorem GUE_T_smul (d : Dims) (N : ℕ) (U : Matrix (d.Idx N) (d.Idx N) ℂ) (c : ℝ)
    (x : GUESlot d N → ℝ) : GUE_T d N U (c • x) = c • GUE_T d N U x := by
  unfold GUE_T
  rw [GUEReconSlot_smul, GUEConj_smul, GUEExtractSlot_smul]

private theorem GUE_T_left_inv (d : Dims) (N : ℕ) {U : Matrix (d.Idx N) (d.Idx N) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (d.Idx N) ℂ) (x : GUESlot d N → ℝ) :
    GUE_T d N Uᴴ (GUE_T d N U x) = x := by
  unfold GUE_T
  rw [GUEReconSlot_GUEExtractSlot d N
    (GUEConj_isHermitian d N U (GUEReconSlot_isHermitian d N x)),
    GUEConj_conj_left d N hU, GUEExtractSlot_GUEReconSlot]

private theorem GUE_T_right_inv (d : Dims) (N : ℕ) {U : Matrix (d.Idx N) (d.Idx N) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (d.Idx N) ℂ) (x : GUESlot d N → ℝ) :
    GUE_T d N U (GUE_T d N Uᴴ x) = x := by
  unfold GUE_T
  rw [GUEReconSlot_GUEExtractSlot d N
    (GUEConj_isHermitian d N Uᴴ (GUEReconSlot_isHermitian d N x)),
    GUEConj_conj_right d N hU, GUEExtractSlot_GUEReconSlot]

/-- **Conjugation-invariance of `Tr(K²)`**, the algebraic core of unitary invariance. -/
private theorem GUE_trace_conj_inv (d : Dims) (N : ℕ) {U K : Matrix (d.Idx N) (d.Idx N) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (d.Idx N) ℂ) :
    Matrix.trace ((Uᴴ * K * U) * (Uᴴ * K * U)) = Matrix.trace (K * K) := by
  have h1 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  have heq : Uᴴ * K * U * (Uᴴ * K * U) = Uᴴ * (K * K) * U := by
    rw [show Uᴴ * K * U * (Uᴴ * K * U) = Uᴴ * K * (U * Uᴴ) * K * U by
      simp only [Matrix.mul_assoc], h1]
    simp only [Matrix.mul_one, Matrix.mul_assoc]
  rw [heq, Matrix.trace_mul_comm, ← Matrix.mul_assoc, h1, Matrix.one_mul]

/-- **The `Q`-invariance of `GUE_T`**: the weighted sum of squares is preserved by conjugation. -/
private theorem GUE_T_Q_inv (d : Dims) (N : ℕ) {U : Matrix (d.Idx N) (d.Idx N) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (d.Idx N) ℂ) (x : GUESlot d N → ℝ) :
    ∑ p : GUESlot d N, (GUE_T d N U x p) ^ 2 / GUEWt d N p.1 =
      ∑ p : GUESlot d N, (x p) ^ 2 / GUEWt d N p.1 := by
  have hK : (GUEReconSlot d N x).IsHermitian := GUEReconSlot_isHermitian d N x
  have hK' : (GUEConj d N U (GUEReconSlot d N x)).IsHermitian := GUEConj_isHermitian d N U hK
  have e1 : (∑ p : GUESlot d N, (GUE_T d N U x p) ^ 2 / GUEWt d N p.1) =
      (Fintype.card (d.Idx N) : ℝ) * (Matrix.trace (GUEConj d N U (GUEReconSlot d N x) *
        GUEConj d N U (GUEReconSlot d N x))).re :=
    GUEMainIdentity d N hK'
  have e2 : (∑ p : GUESlot d N, (x p) ^ 2 / GUEWt d N p.1) =
      (Fintype.card (d.Idx N) : ℝ) *
        (Matrix.trace (GUEReconSlot d N x * GUEReconSlot d N x)).re := by
    rw [← GUEMainIdentity d N hK]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [show GUEEx d N (GUEReconSlot d N x) p.1 =
        GUEExtractSlot d N (GUEReconSlot d N x) p from rfl,
      GUEExtractSlot_GUEReconSlot]
  rw [e1, e2, show GUEConj d N U (GUEReconSlot d N x) = Uᴴ * GUEReconSlot d N x * U from rfl,
    GUE_trace_conj_inv d N hU]

/-! ### Standardization by the square root of the variance, and the resulting isometry -/

private noncomputable def GUEDv (d : Dims) (N : ℕ) (x : GUESlot d N → ℝ) : GUESlot d N → ℝ :=
  fun p => Real.sqrt (GUEWt d N p.1) * x p

private noncomputable def GUEDvInv (d : Dims) (N : ℕ) (x : GUESlot d N → ℝ) : GUESlot d N → ℝ :=
  fun p => x p / Real.sqrt (GUEWt d N p.1)

private theorem GUEDv_add (d : Dims) (N : ℕ) (x y : GUESlot d N → ℝ) :
    GUEDv d N (x + y) = GUEDv d N x + GUEDv d N y := by
  funext p
  show GUEDv d N (x + y) p = GUEDv d N x p + GUEDv d N y p
  unfold GUEDv
  show Real.sqrt (GUEWt d N p.1) * (x p + y p) = _
  ring

private theorem GUEDv_smul (d : Dims) (N : ℕ) (c : ℝ) (x : GUESlot d N → ℝ) :
    GUEDv d N (c • x) = c • GUEDv d N x := by
  funext p
  show GUEDv d N (c • x) p = c • GUEDv d N x p
  unfold GUEDv
  show Real.sqrt (GUEWt d N p.1) * (c * x p) = c * (Real.sqrt (GUEWt d N p.1) * x p)
  ring

private theorem GUEDvInv_add (d : Dims) (N : ℕ) (x y : GUESlot d N → ℝ) :
    GUEDvInv d N (x + y) = GUEDvInv d N x + GUEDvInv d N y := by
  funext p
  show GUEDvInv d N (x + y) p = GUEDvInv d N x p + GUEDvInv d N y p
  unfold GUEDvInv
  show (x p + y p) / Real.sqrt (GUEWt d N p.1) = _
  ring

private theorem GUEDvInv_smul (d : Dims) (N : ℕ) (c : ℝ) (x : GUESlot d N → ℝ) :
    GUEDvInv d N (c • x) = c • GUEDvInv d N x := by
  funext p
  show GUEDvInv d N (c • x) p = c • GUEDvInv d N x p
  unfold GUEDvInv
  show (c * x p) / Real.sqrt (GUEWt d N p.1) = c * (x p / Real.sqrt (GUEWt d N p.1))
  ring

private theorem GUE_sqrt_ne_zero (d : Dims) (N : ℕ) (q : d.Idx N × d.Idx N × Bool) :
    Real.sqrt (GUEWt d N q) ≠ 0 :=
  ne_of_gt (Real.sqrt_pos.mpr (GUEWt_pos d N q))

private theorem GUEDv_GUEDvInv (d : Dims) (N : ℕ) (x : GUESlot d N → ℝ) :
    GUEDv d N (GUEDvInv d N x) = x := by
  funext p
  show Real.sqrt (GUEWt d N p.1) * (x p / Real.sqrt (GUEWt d N p.1)) = x p
  field_simp [GUE_sqrt_ne_zero d N p.1]

private theorem GUEDvInv_GUEDv (d : Dims) (N : ℕ) (x : GUESlot d N → ℝ) :
    GUEDvInv d N (GUEDv d N x) = x := by
  funext p
  show Real.sqrt (GUEWt d N p.1) * x p / Real.sqrt (GUEWt d N p.1) = x p
  field_simp [GUE_sqrt_ne_zero d N p.1]

/-- The composite `extract ∘ (Uᴴ · ·  · U) ∘ reconstruct`, standardized by the square root of the
slot's variance: the map whose invariance under the pointwise Euclidean quadratic form is
established by `GUE_Tpp_Q`. -/
private noncomputable def GUE_Tpp (d : Dims) (N : ℕ) (U : Matrix (d.Idx N) (d.Idx N) ℂ)
    (x : GUESlot d N → ℝ) : GUESlot d N → ℝ :=
  GUEDvInv d N (GUE_T d N U (GUEDv d N x))

private theorem GUE_Tpp_add (d : Dims) (N : ℕ) (U : Matrix (d.Idx N) (d.Idx N) ℂ)
    (x y : GUESlot d N → ℝ) : GUE_Tpp d N U (x + y) = GUE_Tpp d N U x + GUE_Tpp d N U y := by
  unfold GUE_Tpp
  rw [GUEDv_add, GUE_T_add, GUEDvInv_add]

private theorem GUE_Tpp_smul (d : Dims) (N : ℕ) (U : Matrix (d.Idx N) (d.Idx N) ℂ) (c : ℝ)
    (x : GUESlot d N → ℝ) : GUE_Tpp d N U (c • x) = c • GUE_Tpp d N U x := by
  unfold GUE_Tpp
  rw [GUEDv_smul, GUE_T_smul, GUEDvInv_smul]

private theorem GUE_Tpp_left_inv (d : Dims) (N : ℕ) {U : Matrix (d.Idx N) (d.Idx N) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (d.Idx N) ℂ) (x : GUESlot d N → ℝ) :
    GUE_Tpp d N Uᴴ (GUE_Tpp d N U x) = x := by
  unfold GUE_Tpp
  rw [GUEDv_GUEDvInv, GUE_T_left_inv d N hU, GUEDvInv_GUEDv]

private theorem GUE_Tpp_right_inv (d : Dims) (N : ℕ) {U : Matrix (d.Idx N) (d.Idx N) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (d.Idx N) ℂ) (x : GUESlot d N → ℝ) :
    GUE_Tpp d N U (GUE_Tpp d N Uᴴ x) = x := by
  unfold GUE_Tpp
  rw [GUEDv_GUEDvInv, GUE_T_right_inv d N hU, GUEDvInv_GUEDv]

/-- **The pointwise sum of squares is preserved by `GUE_Tpp`.** -/
private theorem GUE_Tpp_Q (d : Dims) (N : ℕ) {U : Matrix (d.Idx N) (d.Idx N) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (d.Idx N) ℂ) (x : GUESlot d N → ℝ) :
    ∑ p : GUESlot d N, (GUE_Tpp d N U x p) ^ 2 = ∑ p : GUESlot d N, (x p) ^ 2 := by
  have key := GUE_T_Q_inv d N hU (GUEDv d N x)
  have hlhs : ∀ p : GUESlot d N, (GUE_Tpp d N U x p) ^ 2 =
      (GUE_T d N U (GUEDv d N x) p) ^ 2 / GUEWt d N p.1 := by
    intro p
    show (GUE_T d N U (GUEDv d N x) p / Real.sqrt (GUEWt d N p.1)) ^ 2 = _
    rw [div_pow, Real.sq_sqrt (GUEWt_pos d N p.1).le]
  have hrhs : ∀ p : GUESlot d N, (GUEDv d N x p) ^ 2 / GUEWt d N p.1 = (x p) ^ 2 := by
    intro p
    show (Real.sqrt (GUEWt d N p.1) * x p) ^ 2 / GUEWt d N p.1 = (x p) ^ 2
    rw [mul_pow, Real.sq_sqrt (GUEWt_pos d N p.1).le]
    field_simp [ne_of_gt (GUEWt_pos d N p.1)]
  simp_rw [hlhs]
  rw [key]
  simp_rw [hrhs]

/-! ### The `EuclideanSpace` isometry, and its relation to `GUE_T` -/

private noncomputable def GUE_Tpp_lin (d : Dims) (N : ℕ) (U : Matrix (d.Idx N) (d.Idx N) ℂ) :
    (GUESlot d N → ℝ) →ₗ[ℝ] (GUESlot d N → ℝ) where
  toFun := GUE_Tpp d N U
  map_add' := GUE_Tpp_add d N U
  map_smul' := GUE_Tpp_smul d N U

private noncomputable def GUE_Tpp_linEquiv (d : Dims) (N : ℕ) {U : Matrix (d.Idx N) (d.Idx N) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (d.Idx N) ℂ) :
    (GUESlot d N → ℝ) ≃ₗ[ℝ] (GUESlot d N → ℝ) :=
  LinearEquiv.ofLinear (GUE_Tpp_lin d N U) (GUE_Tpp_lin d N Uᴴ)
    (LinearMap.ext (fun x => GUE_Tpp_right_inv d N hU x))
    (LinearMap.ext (fun x => GUE_Tpp_left_inv d N hU x))

private noncomputable def GUE_Tpp_eucl (d : Dims) (N : ℕ) {U : Matrix (d.Idx N) (d.Idx N) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (d.Idx N) ℂ) :
    EuclideanSpace ℝ (GUESlot d N) ≃ₗ[ℝ] EuclideanSpace ℝ (GUESlot d N) :=
  (WithLp.linearEquiv 2 ℝ (GUESlot d N → ℝ)).trans
    ((GUE_Tpp_linEquiv d N hU).trans (WithLp.linearEquiv 2 ℝ (GUESlot d N → ℝ)).symm)

private theorem GUE_Tpp_eucl_apply (d : Dims) (N : ℕ) {U : Matrix (d.Idx N) (d.Idx N) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (d.Idx N) ℂ) (z : EuclideanSpace ℝ (GUESlot d N)) (p : GUESlot d N) :
    (GUE_Tpp_eucl d N hU z) p = GUE_Tpp d N U (fun q => z q) p := rfl

private theorem GUE_Tpp_eucl_norm_sq (d : Dims) (N : ℕ) {U : Matrix (d.Idx N) (d.Idx N) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (d.Idx N) ℂ) (z : EuclideanSpace ℝ (GUESlot d N)) :
    ‖GUE_Tpp_eucl d N hU z‖ ^ 2 = ‖z‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp_rw [GUE_Tpp_eucl_apply d N hU]
  exact GUE_Tpp_Q d N hU (fun q => z q)

private theorem GUE_Tpp_eucl_norm (d : Dims) (N : ℕ) {U : Matrix (d.Idx N) (d.Idx N) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (d.Idx N) ℂ) (z : EuclideanSpace ℝ (GUESlot d N)) :
    ‖GUE_Tpp_eucl d N hU z‖ = ‖z‖ := by
  have h := congrArg Real.sqrt (GUE_Tpp_eucl_norm_sq d N hU z)
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h

private noncomputable def GUE_Tpp_isometry (d : Dims) (N : ℕ) {U : Matrix (d.Idx N) (d.Idx N) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (d.Idx N) ℂ) :
    EuclideanSpace ℝ (GUESlot d N) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (GUESlot d N) :=
  { GUE_Tpp_eucl d N hU with norm_map' := GUE_Tpp_eucl_norm d N hU }

/-- **`GUE_T` factors through `GUE_Tpp` via the standardizing scale.** -/
private theorem GUE_T_eq_Tpp (d : Dims) (N : ℕ) (U : Matrix (d.Idx N) (d.Idx N) ℂ)
    (y : GUESlot d N → ℝ) :
    GUE_T d N U y = GUEDv d N (GUE_Tpp d N U (GUEDvInv d N y)) := by
  unfold GUE_Tpp
  rw [GUEDv_GUEDvInv, GUEDv_GUEDvInv]

/-- **The intertwining identity**: reconstructing after `GUE_T` matches conjugating after
reconstructing, for *any* slot values (no Hermitian hypothesis needed: `GUEReconSlot`'s output is
always Hermitian). -/
private theorem GUE_T_intertwine (d : Dims) (N : ℕ) (U : Matrix (d.Idx N) (d.Idx N) ℂ)
    (x : GUESlot d N → ℝ) :
    GUEReconSlot d N (GUE_T d N U x) = GUEConj d N U (GUEReconSlot d N x) := by
  unfold GUE_T
  exact GUEReconSlot_GUEExtractSlot d N
    (GUEConj_isHermitian d N U (GUEReconSlot_isHermitian d N x))

/-! ### The coordinate-restriction map and its law under `gueMeasure` -/

private theorem GUE_f_injective (d : Dims) (N : ℕ) :
    Function.Injective (fun p : GUESlot d N => (⟨N, p.1⟩ : Coord d)) := by
  intro p q h
  simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at h
  exact Subtype.ext h

private theorem Xmat_eq_GUERe_raw (d : Dims) (N : ℕ) (ω : Ω d) :
    Xmat d N ω = GUERe d N (fun q => ω (⟨N, q⟩ : Coord d)) := by
  ext i j
  rcases idxKey_lt_or_eq_or_lt d N i j with h | h | h
  · rw [GUERe_apply_lt d N _ h]
    simp [Xmat_apply, Xentry, h]
  · subst h
    rw [GUERe_apply_diag d N _ i]
    simp [Xmat_apply, Xentry]
  · rw [GUERe_apply_gt d N _ h]
    simp [Xmat_apply, Xentry, h, asymm h]

private theorem Xmat_eq_GUEReconSlot (d : Dims) (N : ℕ) (ω : Ω d) :
    Xmat d N ω =
      GUEReconSlot d N (fun p : GUESlot d N => ω (⟨N, p.1⟩ : Coord d)) := by
  rw [Xmat_eq_GUERe_raw]
  refine GUERe_congr_slots d N (fun q hq => ?_)
  unfold GUEExtend
  rw [dif_pos hq]

/-! ### Measurability of the finite-dimensional maps -/

private theorem measurable_GUERe (d : Dims) (N : ℕ) :
    Measurable (GUERe d N) := by
  apply measurable_pi_iff.mpr; intro i
  apply measurable_pi_iff.mpr; intro j
  simp only [GUERe, Matrix.of_apply]
  split_ifs <;> fun_prop

private theorem measurable_GUEExtend (d : Dims) (N : ℕ) :
    Measurable (GUEExtend d N) := by
  apply measurable_pi_iff.mpr; intro q
  unfold GUEExtend
  split_ifs <;> fun_prop

private theorem measurable_GUEReconSlot (d : Dims) (N : ℕ) :
    Measurable (GUEReconSlot d N) :=
  (measurable_GUERe d N).comp (measurable_GUEExtend d N)

private theorem measurable_GUEConj (d : Dims) (N : ℕ) (U : Matrix (d.Idx N) (d.Idx N) ℂ) :
    Measurable (GUEConj d N U) := by
  apply measurable_pi_iff.mpr; intro i
  apply measurable_pi_iff.mpr; intro j
  unfold GUEConj
  fun_prop

private theorem measurable_GUEExtractSlot (d : Dims) (N : ℕ) :
    Measurable (GUEExtractSlot d N) := by
  apply measurable_pi_iff.mpr; intro p
  unfold GUEExtractSlot GUEEx
  split_ifs <;> fun_prop

private theorem measurable_GUE_T (d : Dims) (N : ℕ) (U : Matrix (d.Idx N) (d.Idx N) ℂ) :
    Measurable (GUE_T d N U) :=
  (measurable_GUEExtractSlot d N).comp
    ((measurable_GUEConj d N U).comp (measurable_GUEReconSlot d N))

/-! ### The law of the coordinate-restriction map, identified with a standardized `stdGaussian` -/

private theorem measurable_GUEDv (d : Dims) (N : ℕ) : Measurable (GUEDv d N) := by
  apply measurable_pi_iff.mpr; intro p
  unfold GUEDv
  fun_prop

private theorem continuous_WithLp_linearEquiv (d : Dims) (N : ℕ) :
    Continuous (⇑(WithLp.linearEquiv 2 ℝ (GUESlot d N → ℝ))) :=
  (WithLp.linearEquiv 2 ℝ (GUESlot d N → ℝ)).toLinearMap.continuous_of_finiteDimensional

private theorem continuous_WithLp_toLp (d : Dims) (N : ℕ) :
    Continuous (WithLp.toLp 2 : (GUESlot d N → ℝ) → EuclideanSpace ℝ (GUESlot d N)) := by
  rw [← WithLp.coe_symm_linearEquiv (K := ℝ)]
  exact (WithLp.linearEquiv 2 ℝ (GUESlot d N → ℝ)).symm.toLinearMap.continuous_of_finiteDimensional

private theorem GUE_gaussianReal_eq (d : Dims) (N : ℕ) (p : GUESlot d N) :
    (gaussianReal 0 1).map (fun t => Real.sqrt (GUEWt d N p.1) * t) =
      gaussianReal 0 (gueCoordVar d N (⟨N, p.1⟩ : Coord d)) := by
  rw [gaussianReal_map_const_mul]
  congr 1
  · ring
  · apply NNReal.eq
    show (Real.sqrt (GUEWt d N p.1)) ^ 2 * 1 = (gueCoordVar d N (⟨N, p.1⟩ : Coord d) : ℝ)
    rw [Real.sq_sqrt (GUEWt_pos d N p.1).le, mul_one]
    rfl

private theorem GUE_muI_eq (d : Dims) (N : ℕ) :
    (gueMeasure d N).map (fun ω => fun p : GUESlot d N => ω (⟨N, p.1⟩ : Coord d)) =
      Measure.pi (fun p : GUESlot d N => gaussianReal 0 (gueCoordVar d N (⟨N, p.1⟩ : Coord d))) := by
  unfold gueMeasure
  rw [Measure.map_infinitePi_infinitePi_of_inj (GUE_f_injective d N), Measure.infinitePi_eq_pi]

private theorem GUE_muI_eq_stdGaussian_map (d : Dims) (N : ℕ) :
    Measure.pi (fun p : GUESlot d N => gaussianReal 0 (gueCoordVar d N (⟨N, p.1⟩ : Coord d))) =
      (stdGaussian (EuclideanSpace ℝ (GUESlot d N))).map
        (GUEDv d N ∘ ⇑(WithLp.linearEquiv 2 ℝ (GUESlot d N → ℝ))) := by
  have hpi : (Measure.pi fun _ : GUESlot d N => gaussianReal 0 1).map (GUEDv d N) =
      Measure.pi (fun p : GUESlot d N => gaussianReal 0 (gueCoordVar d N (⟨N, p.1⟩ : Coord d))) := by
    rw [show (GUEDv d N) = (fun x p => Real.sqrt (GUEWt d N p.1) * x p) from rfl,
      Measure.pi_map_pi (fun p => Measurable.aemeasurable (by fun_prop))]
    exact congrArg Measure.pi (funext fun p => GUE_gaussianReal_eq d N p)
  have hstd : (Measure.pi fun _ : GUESlot d N => gaussianReal 0 1) =
      (stdGaussian (EuclideanSpace ℝ (GUESlot d N))).map
        (⇑(WithLp.linearEquiv 2 ℝ (GUESlot d N → ℝ))) := by
    rw [← map_pi_eq_stdGaussian, Measure.map_map (continuous_WithLp_linearEquiv d N).measurable
      (continuous_WithLp_toLp d N).measurable]
    have hid : (⇑(WithLp.linearEquiv 2 ℝ (GUESlot d N → ℝ)) ∘ WithLp.toLp 2) =
        (id : (GUESlot d N → ℝ) → GUESlot d N → ℝ) := by
      funext x
      show WithLp.ofLp (WithLp.toLp 2 x) = x
      rfl
    rw [hid, Measure.map_id]
  rw [← hpi, hstd, Measure.map_map (measurable_GUEDv d N)
    (continuous_WithLp_linearEquiv d N).measurable]

private theorem GUE_muI_eq_final (d : Dims) (N : ℕ) :
    (gueMeasure d N).map (fun ω => fun p : GUESlot d N => ω (⟨N, p.1⟩ : Coord d)) =
      (stdGaussian (EuclideanSpace ℝ (GUESlot d N))).map
        (GUEDv d N ∘ ⇑(WithLp.linearEquiv 2 ℝ (GUESlot d N → ℝ))) := by
  rw [GUE_muI_eq, GUE_muI_eq_stdGaussian_map]

/-- **Invariance of the coordinate law under `GUE_T`.** -/
private theorem GUE_muI_invariant (d : Dims) (N : ℕ) {U : Matrix (d.Idx N) (d.Idx N) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (d.Idx N) ℂ) :
    ((gueMeasure d N).map (fun ω => fun p : GUESlot d N => ω (⟨N, p.1⟩ : Coord d))).map
        (GUE_T d N U) =
      (gueMeasure d N).map (fun ω => fun p : GUESlot d N => ω (⟨N, p.1⟩ : Coord d)) := by
  rw [GUE_muI_eq_final]
  rw [Measure.map_map (measurable_GUE_T d N U)
    ((measurable_GUEDv d N).comp (continuous_WithLp_linearEquiv d N).measurable)]
  have hfun : GUE_T d N U ∘ (GUEDv d N ∘ ⇑(WithLp.linearEquiv 2 ℝ (GUESlot d N → ℝ))) =
      (GUEDv d N ∘ ⇑(WithLp.linearEquiv 2 ℝ (GUESlot d N → ℝ))) ∘ (GUE_Tpp_isometry d N hU) := by
    funext z
    show GUE_T d N U (GUEDv d N ((WithLp.linearEquiv 2 ℝ (GUESlot d N → ℝ)) z)) =
      GUEDv d N ((WithLp.linearEquiv 2 ℝ (GUESlot d N → ℝ)) (GUE_Tpp_isometry d N hU z))
    rw [GUE_T_eq_Tpp]
    congr 1
    show GUE_Tpp d N U (GUEDvInv d N (GUEDv d N ((WithLp.linearEquiv 2 ℝ _) z))) = _
    rw [GUEDvInv_GUEDv]
    rfl
  rw [hfun, ← Measure.map_map
    ((measurable_GUEDv d N).comp (continuous_WithLp_linearEquiv d N).measurable)
    (LinearIsometryEquiv.continuous _).measurable, stdGaussian_map (GUE_Tpp_isometry d N hU)]

/-! ### Target 1: `gueMeasure_map_conj` -/

/-- **G4-2, target 1.** The standard GUE law is invariant under conjugation by any fixed
unitary matrix. -/
theorem gueMeasure_map_conj (d : Dims) (N : ℕ) {U : Matrix (d.Idx N) (d.Idx N) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (d.Idx N) ℂ) :
    (gueMeasure d N).map (fun ω => Uᴴ * Xmat d N ω * U) = (gueMeasure d N).map (Xmat d N) := by
  have hr_meas : Measurable (fun ω : Ω d => fun p : GUESlot d N => ω (⟨N, p.1⟩ : Coord d)) := by
    apply measurable_pi_iff.mpr; intro p; exact measurable_pi_apply _
  have key1 : (fun ω => Uᴴ * Xmat d N ω * U) =
      (GUEConj d N U ∘ GUEReconSlot d N) ∘
        (fun ω : Ω d => fun p : GUESlot d N => ω (⟨N, p.1⟩ : Coord d)) := by
    funext ω
    show Uᴴ * Xmat d N ω * U =
      GUEConj d N U (GUEReconSlot d N (fun p : GUESlot d N => ω (⟨N, p.1⟩ : Coord d)))
    rw [Xmat_eq_GUEReconSlot d N ω]
    rfl
  have key2 : Xmat d N =
      GUEReconSlot d N ∘ (fun ω : Ω d => fun p : GUESlot d N => ω (⟨N, p.1⟩ : Coord d)) :=
    funext (Xmat_eq_GUEReconSlot d N)
  rw [key1, key2,
    ← Measure.map_map ((measurable_GUEConj d N U).comp (measurable_GUEReconSlot d N)) hr_meas,
    ← Measure.map_map (measurable_GUEReconSlot d N) hr_meas,
    show GUEConj d N U ∘ GUEReconSlot d N = GUEReconSlot d N ∘ GUE_T d N U from
      funext (fun x => (GUE_T_intertwine d N U x).symm),
    ← Measure.map_map (measurable_GUEReconSlot d N) (measurable_GUE_T d N U)]
  congr 1
  exact GUE_muI_invariant d N hU

end RBM.Gauss
