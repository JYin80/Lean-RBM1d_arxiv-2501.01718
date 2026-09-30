/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Flow.OUMarginalGaussian
import Mathlib.Probability.Independence.InfinitePi

/-!
# The `L ≡ 3` band model is the GUE

Formalization support for Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random
Band Matrices*, Theorem 2.6 Step 1.

At `L ≡ 3` blocks every pair of blocks is a neighbour (`sbSupport 3 = univ`), so the block
covariance kernel `S^(B)` is flat: `S_{ij} = 1/(3W) = 1/M` for *every* pair `i, j`, exactly the
GUE variance profile.  This file records that identity of matrix laws (`P_map_Xmat_dL3`), and the
general fact that a principal minor of the GUE along an `idxKey`-order-preserving embedding is a
rescaled smaller GUE (`gueMeasure_map_submatrix`), via an explicit `idxKey`-order-preserving
embedding between any two `Dims.Idx` types whose sizes allow it
(`exists_idxKey_strictMono_embedding`).

`dL3` is defined as `Dims.example` (`RBM1D/Gauss/DimsExample.lean`): the fields are
`W N = max 1 (N/3)`, `L N ≡ 3`, `c = 1/4`, and `Dims.example`'s `dim`/`bandwidth`
proofs already discharge the remaining two `Dims` fields without weakening either.

## Route

Both `P_map_Xmat_dL3` and `gueMeasure_map_submatrix` are proved by pushing the relevant measure
forward through the deterministic, finite-coordinate reconstruction map `coordMat` (a copy, under
this file's own prefix, of the case split used by `Xentry`/`Xmat`), reducing to an identity of
finitely-supported product Gaussian laws via `Measure.map_infinitePi_infinitePi_of_inj`,
`Measure.infinitePi_eq_pi`, `Measure.pi_map_pi` and `gaussianReal_map_const_mul` (all Mathlib).
-/

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Gauss

/-! ### `dL3` -/

/-- The `L ≡ 3` dimensions: three blocks of width `max 1 (N / 3)`, `c = 1/4`.  Reuses
`Dims.example`, whose `dim`/`bandwidth` proofs are not weakened. -/
noncomputable def dL3 : Dims := Dims.example

@[simp] theorem dL3_W (N : ℕ) : dL3.W N = max 1 (N / 3) := Dims.example_W N

@[simp] theorem dL3_L (N : ℕ) : dL3.L N = 3 := Dims.example_L N

theorem ouMatrixSize_dL3 (N : ℕ) : ouMatrixSize dL3 N = 3 * max 1 (N / 3) := by
  simp [ouMatrixSize, dL3_L, dL3_W]

/-! ### `sbSupport 3 = univ`, hence the block kernel is flat at `L ≡ 3` -/

private theorem sbSupport_three : sbSupport 3 = Finset.univ := by decide

private theorem sbKre_three (u : ZMod 3) : sbKre 3 u = 1 / 3 := by
  unfold sbKre
  rw [if_pos (sbSupport_three ▸ Finset.mem_univ u)]

/-- `sbKre_three`, transported along any propositional equality `L = 3` (needed because
`dL3.L N` is only *definitionally*, not syntactically, `3`). -/
private theorem sbKre_of_L_eq_three {L : ℕ} (hL : L = 3) (u : ZMod L) : sbKre L u = 1 / 3 := by
  subst hL
  exact sbKre_three u

/-- At `L ≡ 3`, `S_{ij} = 1/(3W)` for **every** pair `i, j` (not just neighbours): the block
kernel is flat. -/
private theorem Sblk_dL3 (N : ℕ) (i j : dL3.Idx N) :
    Sblk (dL3.L N) (dL3.W N) i j = 1 / (3 * (dL3.W N : ℝ)) := by
  unfold Sblk
  rw [sbKre_of_L_eq_three (dL3_L N) (i.1 - j.1)]
  ring

/-! ### `gvar dL3 = gueCoordVar dL3` pointwise, at every coordinate -/

private theorem gvar_dL3_eq_gueCoordVar (N : ℕ) (q : dL3.Idx N × dL3.Idx N × Bool) :
    gvar dL3 (⟨N, q⟩ : Coord dL3) = gueCoordVar dL3 N (⟨N, q⟩ : Coord dL3) := by
  obtain ⟨i, j, b⟩ := q
  have hM : (ouMatrixSize dL3 N : ℝ) = 3 * (dL3.W N : ℝ) := by
    exact_mod_cast ouMatrixSize_dL3 N
  apply NNReal.eq
  by_cases h : i = j
  · subst h
    rw [gvar_diag, gueCoordVar_diag, Sblk_dL3, hM]
  · rw [gvar_offDiag dL3 N i j b h, gueCoordVar_offDiag dL3 N i j b h, Sblk_dL3, hM]
    ring

/-! ### The deterministic finite-coordinate reconstruction map -/

/-- Rebuild a matrix from a total assignment of real values to triples `(i, j, b)`, using the
same case split as `Xentry`.  File-local copy: the analogous machinery of
`GUEUnitaryInvariance.lean` is `private` there. -/
private noncomputable def coordMat (d : Dims) (N : ℕ) (x : d.Idx N × d.Idx N × Bool → ℝ) :
    Matrix (d.Idx N) (d.Idx N) ℂ :=
  Matrix.of fun i j =>
    if idxKey d N i < idxKey d N j then
      (x (i, j, true) : ℂ) + Complex.I * (x (i, j, false) : ℂ)
    else if idxKey d N j < idxKey d N i then
      (x (j, i, true) : ℂ) - Complex.I * (x (j, i, false) : ℂ)
    else
      (x (i, i, true) : ℂ)

private theorem coordMat_apply_lt (d : Dims) (N : ℕ) (x : d.Idx N × d.Idx N × Bool → ℝ)
    {i j : d.Idx N} (h : idxKey d N i < idxKey d N j) :
    coordMat d N x i j = (x (i, j, true) : ℂ) + Complex.I * (x (i, j, false) : ℂ) := by
  simp only [coordMat, Matrix.of_apply, if_pos h]

private theorem coordMat_apply_gt (d : Dims) (N : ℕ) (x : d.Idx N × d.Idx N × Bool → ℝ)
    {i j : d.Idx N} (h : idxKey d N j < idxKey d N i) :
    coordMat d N x i j = (x (j, i, true) : ℂ) - Complex.I * (x (j, i, false) : ℂ) := by
  have hne : ¬ idxKey d N i < idxKey d N j := asymm h
  simp only [coordMat, Matrix.of_apply, if_neg hne, if_pos h]

private theorem coordMat_apply_diag (d : Dims) (N : ℕ) (x : d.Idx N × d.Idx N × Bool → ℝ)
    (i : d.Idx N) : coordMat d N x i i = (x (i, i, true) : ℂ) := by
  have hne : ¬ idxKey d N i < idxKey d N i := lt_irrefl _
  simp only [coordMat, Matrix.of_apply, if_neg hne]

private theorem measurable_coordMat (d : Dims) (N : ℕ) : Measurable (coordMat d N) := by
  apply measurable_pi_iff.mpr; intro i
  apply measurable_pi_iff.mpr; intro j
  simp only [coordMat, Matrix.of_apply]
  split_ifs <;> fun_prop

private theorem Xmat_eq_coordMat (d : Dims) (N : ℕ) (ω : Ω d) :
    Xmat d N ω = coordMat d N (fun q => ω (⟨N, q⟩ : Coord d)) := by
  ext i j
  rcases idxKey_lt_or_eq_or_lt d N i j with h | h | h
  · rw [coordMat_apply_lt d N _ h]
    simp [Xmat_apply, Xentry, h]
  · subst h
    rw [coordMat_apply_diag d N _ i]
    simp [Xmat_apply, Xentry]
  · rw [coordMat_apply_gt d N _ h]
    simp [Xmat_apply, Xentry, h, asymm h]

private theorem measurable_coordVec (d : Dims) (N : ℕ) :
    Measurable (fun ω : Ω d => fun q : d.Idx N × d.Idx N × Bool => ω (⟨N, q⟩ : Coord d)) := by
  apply measurable_pi_iff.mpr; intro q
  exact measurable_pi_apply _

private theorem sigmaMk_injective (d : Dims) (N : ℕ) :
    Function.Injective (fun q : d.Idx N × d.Idx N × Bool => (⟨N, q⟩ : Coord d)) := by
  intro q q' h
  simpa using h

/-! ### The joint law of the level-`N` coordinates, for `P` and for `gueMeasure` -/

private theorem P_map_coords (d : Dims) (N : ℕ) :
    (P d).map (fun ω q => ω (⟨N, q⟩ : Coord d)) =
      Measure.pi (fun q : d.Idx N × d.Idx N × Bool => gaussianReal 0 (gvar d ⟨N, q⟩)) := by
  unfold P
  rw [Measure.map_infinitePi_infinitePi_of_inj (sigmaMk_injective d N),
    Measure.infinitePi_eq_pi]

private theorem gueMeasure_map_coords (d : Dims) (N : ℕ) :
    (gueMeasure d N).map (fun ω q => ω (⟨N, q⟩ : Coord d)) =
      Measure.pi (fun q : d.Idx N × d.Idx N × Bool => gaussianReal 0 (gueCoordVar d N ⟨N, q⟩)) := by
  unfold gueMeasure
  rw [Measure.map_infinitePi_infinitePi_of_inj (sigmaMk_injective d N),
    Measure.infinitePi_eq_pi]

/-! ### Target 1 -/

/-- **G4-7b, target 1.** At `L ≡ 3` every block pair is a neighbour (`sbSupport 3 = univ`), so
`S ≡ 1/(3W) = 1/M`: the band matrix is the GUE. -/
theorem P_map_Xmat_dL3 (N : ℕ) :
    (P dL3).map (Xmat dL3 N) = (gueMeasure dL3 N).map (Xmat dL3 N) := by
  have hcomp : Xmat dL3 N = coordMat dL3 N ∘ (fun ω q => ω (⟨N, q⟩ : Coord dL3)) :=
    funext (Xmat_eq_coordMat dL3 N)
  have hP : (P dL3).map (Xmat dL3 N) =
      ((P dL3).map (fun ω q => ω (⟨N, q⟩ : Coord dL3))).map (coordMat dL3 N) := by
    rw [hcomp, Measure.map_map (measurable_coordMat dL3 N) (measurable_coordVec dL3 N)]
  have hG : (gueMeasure dL3 N).map (Xmat dL3 N) =
      ((gueMeasure dL3 N).map (fun ω q => ω (⟨N, q⟩ : Coord dL3))).map (coordMat dL3 N) := by
    rw [hcomp, Measure.map_map (measurable_coordMat dL3 N) (measurable_coordVec dL3 N)]
  have hvar : (fun q : dL3.Idx N × dL3.Idx N × Bool => gaussianReal 0 (gvar dL3 ⟨N, q⟩)) =
      (fun q => gaussianReal 0 (gueCoordVar dL3 N ⟨N, q⟩)) := by
    funext q
    rw [gvar_dL3_eq_gueCoordVar N q]
  rw [hP, hG, P_map_coords, gueMeasure_map_coords, hvar]

/-! ### Target 3: an explicit `idxKey`-order-preserving embedding -/

private theorem idxKey_lt_ouMatrixSize (d : Dims) (N : ℕ) (i : d.Idx N) :
    idxKey d N i < ouMatrixSize d N := by
  obtain ⟨a, α⟩ := i
  have ha : a.val < d.L N := ZMod.val_lt a
  have hα : (α : ℕ) < d.W N := α.isLt
  have h1 : d.W N * a.val + (α : ℕ) < d.W N * a.val + d.W N := by omega
  have h2 : d.W N * a.val + d.W N ≤ d.W N * d.L N := by
    have hmul : d.W N * (a.val + 1) ≤ d.W N * d.L N := Nat.mul_le_mul_left _ (by omega)
    calc d.W N * a.val + d.W N = d.W N * (a.val + 1) := by ring
      _ ≤ d.W N * d.L N := hmul
  have h3 : d.W N * a.val + (α : ℕ) < d.W N * d.L N := lt_of_lt_of_le h1 h2
  unfold idxKey ouMatrixSize
  rw [Nat.mul_comm (d.L N) (d.W N)]
  exact h3

/-- The explicit right inverse of `idxKey`: `k ↦ (k / W, k % W)`. -/
private noncomputable def unkey (d' : Dims) (N' : ℕ) (k : ℕ) : d'.Idx N' :=
  (((k / d'.W N' : ℕ) : ZMod (d'.L N')),
    (⟨k % d'.W N', Nat.mod_lt k (d'.W_pos N')⟩ : Fin (d'.W N')))

private theorem idxKey_unkey (d' : Dims) (N' : ℕ) (k : ℕ) (hk : k < ouMatrixSize d' N') :
    idxKey d' N' (unkey d' N' k) = k := by
  have hWpos : 0 < d'.W N' := d'.W_pos N'
  have hk' : k < d'.L N' * d'.W N' := hk
  have hdiv : k / d'.W N' < d'.L N' := by
    rw [Nat.div_lt_iff_lt_mul hWpos]
    omega
  unfold idxKey unkey
  dsimp only
  rw [ZMod.val_cast_of_lt hdiv]
  exact Nat.div_add_mod k (d'.W N')

/-- The explicit `idxKey`-order-preserving embedding `unkey d' N' ∘ idxKey d N`, well-defined
whenever the target has room (`h`). -/
private noncomputable def embedFun (d d' : Dims) (N N' : ℕ) (i : d.Idx N) : d'.Idx N' :=
  unkey d' N' (idxKey d N i)

private theorem idxKey_embedFun (d d' : Dims) (N N' : ℕ) (h : ouMatrixSize d N ≤ ouMatrixSize d' N')
    (i : d.Idx N) : idxKey d' N' (embedFun d d' N N' i) = idxKey d N i :=
  idxKey_unkey d' N' (idxKey d N i) (lt_of_lt_of_le (idxKey_lt_ouMatrixSize d N i) h)

private theorem embedFun_injective (d d' : Dims) (N N' : ℕ)
    (h : ouMatrixSize d N ≤ ouMatrixSize d' N') :
    Function.Injective (embedFun d d' N N' : d.Idx N → d'.Idx N') := by
  intro i j hij
  have : idxKey d N i = idxKey d N j := by
    rw [← idxKey_embedFun d d' N N' h i, ← idxKey_embedFun d d' N N' h j, hij]
  exact idxKey_injective d N this

/-- **G4-7b, target 3.** An `idxKey`-strictly-monotone embedding exists whenever the sizes
allow it. -/
theorem exists_idxKey_strictMono_embedding (d d' : Dims) (N N' : ℕ)
    (h : ouMatrixSize d N ≤ ouMatrixSize d' N') :
    ∃ e : d.Idx N ↪ d'.Idx N', ∀ i j : d.Idx N,
      idxKey d N i < idxKey d N j → idxKey d' N' (e i) < idxKey d' N' (e j) := by
  refine ⟨⟨embedFun d d' N N', embedFun_injective d d' N N' h⟩, fun i j hij => ?_⟩
  change idxKey d' N' (embedFun d d' N N' i) < idxKey d' N' (embedFun d d' N N' j)
  rw [idxKey_embedFun d d' N N' h i, idxKey_embedFun d d' N N' h j]
  exact hij

/-! ### Target 4: a principal minor of the GUE is a rescaled smaller GUE -/

/-- The coordinates of `d'` at level `N'` read by the principal minor along `e`: the triple
`(i, j, b)` of `d` is sent to `⟨N', e i, e j, b⟩`. -/
private def minorCoord (d d' : Dims) (N N' : ℕ) (e : d.Idx N ↪ d'.Idx N')
    (q : d.Idx N × d.Idx N × Bool) : Coord d' :=
  ⟨N', e q.1, e q.2.1, q.2.2⟩

private theorem minorCoord_injective (d d' : Dims) (N N' : ℕ) (e : d.Idx N ↪ d'.Idx N') :
    Function.Injective (minorCoord d d' N N' e) := by
  rintro ⟨i, j, b⟩ ⟨i', j', b'⟩ h
  simp only [minorCoord, Sigma.mk.injEq, heq_eq_eq, true_and, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  rw [e.injective h1, e.injective h2, h3]

private theorem measurable_minorVec (d d' : Dims) (N N' : ℕ) (e : d.Idx N ↪ d'.Idx N') :
    Measurable (fun ω : Ω d' => fun q : d.Idx N × d.Idx N × Bool =>
      ω (minorCoord d d' N N' e q)) := by
  apply measurable_pi_iff.mpr; intro q
  exact measurable_pi_apply _

/-- The principal minor of `Xmat d' N'` along an `idxKey`-monotone embedding is `coordMat d N`
applied to the coordinates `⟨N', e i, e j, b⟩`. -/
private theorem submatrix_eq_coordMat (d d' : Dims) (N N' : ℕ) (e : d.Idx N ↪ d'.Idx N')
    (he : ∀ i j : d.Idx N, idxKey d N i < idxKey d N j → idxKey d' N' (e i) < idxKey d' N' (e j))
    (ω : Ω d') :
    (Xmat d' N' ω).submatrix e e = coordMat d N (fun q => ω (minorCoord d d' N N' e q)) := by
  ext i j
  rw [Matrix.submatrix_apply]
  rcases idxKey_lt_or_eq_or_lt d N i j with h | h | h
  · rw [coordMat_apply_lt d N _ h]
    have h' := he i j h
    simp [Xmat_apply, Xentry, h', minorCoord]
  · subst h
    rw [coordMat_apply_diag d N _ i]
    simp [Xmat_apply, Xentry, minorCoord]
  · rw [coordMat_apply_gt d N _ h]
    have h' := he j i h
    simp [Xmat_apply, Xentry, h', asymm h', minorCoord]

/-- `coordMat` is real-homogeneous. -/
private theorem coordMat_const_mul (d : Dims) (N : ℕ) (s : ℝ)
    (x : d.Idx N × d.Idx N × Bool → ℝ) :
    coordMat d N (fun q => s * x q) = (s : ℂ) • coordMat d N x := by
  ext i j
  rcases idxKey_lt_or_eq_or_lt d N i j with h | h | h
  · rw [coordMat_apply_lt d N _ h, Matrix.smul_apply, coordMat_apply_lt d N _ h]
    simp only [smul_eq_mul, Complex.ofReal_mul]
    ring
  · subst h
    rw [coordMat_apply_diag d N _ i, Matrix.smul_apply, coordMat_apply_diag d N _ i]
    simp only [smul_eq_mul, Complex.ofReal_mul]
  · rw [coordMat_apply_gt d N _ h, Matrix.smul_apply, coordMat_apply_gt d N _ h]
    simp only [smul_eq_mul, Complex.ofReal_mul]
    ring

/-- The variance of the coordinate read through the embedding equals `M/M'` times the variance
of the corresponding coordinate of the smaller GUE (real-valued form, to avoid building an
`ℝ≥0` term via an anonymous constructor). -/
private theorem minor_var_eq (d d' : Dims) (N N' : ℕ) (e : d.Idx N ↪ d'.Idx N')
    (q : d.Idx N × d.Idx N × Bool) :
    (gueCoordVar d' N' (minorCoord d d' N N' e q) : ℝ) =
      ((ouMatrixSize d N : ℝ) / (ouMatrixSize d' N' : ℝ)) *
        (gueCoordVar d N (⟨N, q⟩ : Coord d) : ℝ) := by
  obtain ⟨i, j, b⟩ := q
  have hM : (0 : ℝ) < (ouMatrixSize d N : ℝ) := by exact_mod_cast ouMatrixSize_pos d N
  have hM' : (0 : ℝ) < (ouMatrixSize d' N' : ℝ) := by exact_mod_cast ouMatrixSize_pos d' N'
  unfold minorCoord
  dsimp only
  by_cases h : i = j
  · subst h
    rw [gueCoordVar_diag, gueCoordVar_diag]
    field_simp
  · have hne : e i ≠ e j := fun h' => h (e.injective h')
    rw [gueCoordVar_offDiag d' N' (e i) (e j) b hne, gueCoordVar_offDiag d N i j b h]
    field_simp

/-- **G4-7b, target 4.** A principal minor of the GUE of size `M'` along an `idxKey`-monotone
embedding is `√(M/M')` times the GUE of size `M`. -/
theorem gueMeasure_map_submatrix (d d' : Dims) (N N' : ℕ) (e : d.Idx N ↪ d'.Idx N')
    (he : ∀ i j : d.Idx N, idxKey d N i < idxKey d N j → idxKey d' N' (e i) < idxKey d' N' (e j)) :
    (gueMeasure d' N').map (fun ω => (Xmat d' N' ω).submatrix e e) =
      (gueMeasure d N).map (fun ω =>
        ((Real.sqrt ((ouMatrixSize d N : ℝ) / (ouMatrixSize d' N' : ℝ)) : ℝ) : ℂ) •
          Xmat d N ω) := by
  set c₀ : ℝ := Real.sqrt ((ouMatrixSize d N : ℝ) / (ouMatrixSize d' N' : ℝ)) with hc₀
  have hsq : c₀ ^ 2 = (ouMatrixSize d N : ℝ) / (ouMatrixSize d' N' : ℝ) := by
    rw [hc₀]; exact Real.sq_sqrt (by positivity)
  have hscale : Measurable (fun (x : d.Idx N × d.Idx N × Bool → ℝ) (q : d.Idx N × d.Idx N × Bool) =>
      c₀ * x q) := by
    apply measurable_pi_iff.mpr; intro q
    fun_prop
  have hL : (fun ω : Ω d' => (Xmat d' N' ω).submatrix e e) =
      coordMat d N ∘ (fun ω q => ω (minorCoord d d' N N' e q)) :=
    funext (submatrix_eq_coordMat d d' N N' e he)
  have hR : (fun ω : Ω d => (c₀ : ℂ) • Xmat d N ω) =
      coordMat d N ∘ ((fun (x : d.Idx N × d.Idx N × Bool → ℝ) q => c₀ * x q) ∘
        (fun ω q => ω (⟨N, q⟩ : Coord d))) := by
    funext ω
    simp only [Function.comp]
    rw [Xmat_eq_coordMat, coordMat_const_mul]
  have hA : (gueMeasure d' N').map (fun ω q => ω (minorCoord d d' N N' e q)) =
      ((gueMeasure d N).map (fun ω q => ω (⟨N, q⟩ : Coord d))).map
        (fun (x : d.Idx N × d.Idx N × Bool → ℝ) q => c₀ * x q) := by
    rw [gueMeasure_map_coords, Measure.pi_map_pi (fun q => Measurable.aemeasurable (by fun_prop))]
    unfold gueMeasure
    rw [Measure.map_infinitePi_infinitePi_of_inj (minorCoord_injective d d' N N' e),
      Measure.infinitePi_eq_pi]
    congr 1
    funext q
    rw [gaussianReal_map_const_mul, mul_zero]
    congr 1
    apply NNReal.eq
    rw [NNReal.coe_mul, NNReal.coe_mk, minor_var_eq d d' N N' e q, hsq]
  rw [hL, hR, ← Measure.map_map (measurable_coordMat d N) (measurable_minorVec d d' N N' e),
    ← Measure.map_map (measurable_coordMat d N) (hscale.comp (measurable_coordVec d N)),
    ← Measure.map_map hscale (measurable_coordVec d N), hA]

/-! ### Acceptance-criterion witness: a genuine `M < M'` instance at `dL3` -/

end RBM.Gauss
