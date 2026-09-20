/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.LDEQuadT
import RBM1D.Gauss.RowIndep
import RBM1D.Gauss.LDEHyp
import RBM1D.Loop.Split

/-!
# The row chaos of the Gaussian model — T95

`RBM1D/Gauss/LDEQuad.lean` develops the quadratic large deviation estimate for an abstract
`RBM.Gauss.RowChaos`, and its header lists "the instance" as one of the things not done there.
This file builds it.

## The one design decision

`RowChaos` requires the matrix `B` to be **globally bounded** and **continuous** and to **read
no coordinate of the row**.  The obvious candidate, `greenMinor G i = G_{kl} - G_{ki}G_{il}/G_{ii}`,
fails the first: `G_{ii}` has no global lower bound (only `Im G_{ii} = Im z\,\|Ge_i\|^2 > 0`).

The fix is to take `B` to be the **minor resolvent** `(H^{(i)} - z)^{-1}` itself:

* bounded by `|Im z|⁻¹`, for every `ω`, by `RBM.Gauss.norm_green_le` applied to the submatrix
  (a submatrix of a Hermitian matrix is Hermitian);
* continuous, because the resolvent of a continuously varying Hermitian matrix is continuous
  off the real axis;
* manifestly a function of the off-row block only (`Hflow_submatrix_congr_offRowCoord`).

It *equals* `greenMinor G i` for **every** `ω` — `RBM.inv_minor_resolvent` needs `H - z`
invertible and `G_{ii} ≠ 0`, and both hold unconditionally when `Im z ≠ 0`
(`RBM.isUnit_det_sub_smul_one`, `RBM.green_diag_ne_zero` of T91).  So nothing is lost.

The row data `co`/`eps` is the parametrisation `RBM.Gauss.rowCoord`/`RBM.Gauss.rowSign` of
`Gauss/RowIndep.lean` (T81), and `r = √u`.

## Main statements

* `RBM.Gauss.modelChaos`          : the `RowChaos` instance of the Gaussian model at row `i`
* `RBM.Gauss.modelChaos_h`        : its row is `h_k = (H_u)_{ik}`
* `RBM.Gauss.modelChaos_sg`       : its variance is `σ_k = u S_{ik}`
* `RBM.Gauss.modelChaos_B_eq`     : its matrix is `greenMinor G i`, for every `ω`
-/

namespace RBM.Gauss

open MeasureTheory Matrix Finset

open scoped Matrix.Norms.L2Operator

/-! ### Continuity of the resolvent, for an arbitrary index type

`RBM.Gauss.continuous_green_comp` of `Gauss/Hierarchy.lean` is this statement specialised to
`d.Idx N`; the proof is verbatim the same.  We need it on the minor index `{a // a ≠ i}`. -/

section GreenCont

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The resolvent depends continuously on a continuously varying Hermitian matrix. -/
theorem continuous_green_of_isHermitian {V : Type*} [TopologicalSpace V]
    {f : V → Matrix n n ℂ} (hf : Continuous f) (hherm : ∀ v, (f v).IsHermitian)
    {z : ℂ} (hz : z.im ≠ 0) : Continuous fun v => green (f v) z := by
  rw [continuous_iff_continuousAt]
  intro v
  have hU : IsUnit (f v - z • (1 : Matrix n n ℂ)) :=
    isUnit_sub_smul_one_of_im_ne_zero (hherm v) hz
  have hspec : ((hU.unit : (Matrix n n ℂ)ˣ) : Matrix n n ℂ)
      = f v - z • (1 : Matrix n n ℂ) := IsUnit.unit_spec _
  have h1 : ContinuousAt (Ring.inverse (M₀ := Matrix n n ℂ))
      (f v - z • (1 : Matrix n n ℂ)) := by
    rw [← hspec]
    exact (hasFDerivAt_ringInverse (𝕜 := ℝ) hU.unit).continuousAt
  have h2 : ContinuousAt (fun w => f w - z • (1 : Matrix n n ℂ)) v :=
    hf.continuousAt.sub continuousAt_const
  have := ContinuousAt.comp (g := Ring.inverse (M₀ := Matrix n n ℂ))
    (f := fun w => f w - z • (1 : Matrix n n ℂ)) h1 h2
  simpa [green, Function.comp_def, Matrix.nonsing_inv_eq_ringInverse] using this

end GreenCont

variable {d : Dims} {N : ℕ} {u : ℝ} {z : ℂ}

/-! ### The minor resolvent as the matrix of the chaos -/

/-- `(H^{(i)} - z)^{-1}`, the resolvent of the minor. -/
noncomputable def minorRes (d : Dims) (N : ℕ) (u : ℝ) (z : ℂ) (i : d.Idx N) (ω : Ω d) :
    Matrix {a : d.Idx N // a ≠ i} {a : d.Idx N // a ≠ i} ℂ :=
  green ((Hflow d N u ω).submatrix (Subtype.val : {a : d.Idx N // a ≠ i} → d.Idx N)
    (Subtype.val : {a : d.Idx N // a ≠ i} → d.Idx N)) z

theorem isHermitian_Hflow_submatrix (d : Dims) (N : ℕ) (u : ℝ) (ω : Ω d) (i : d.Idx N) :
    ((Hflow d N u ω).submatrix (Subtype.val : {a : d.Idx N // a ≠ i} → d.Idx N)
      (Subtype.val : {a : d.Idx N // a ≠ i} → d.Idx N)).IsHermitian :=
  (Hflow_isHermitian d N u ω).submatrix _

/-- **The minor resolvent is bounded by `|Im z|⁻¹`, for every `ω`.** -/
theorem norm_minorRes_le (hz : z.im ≠ 0) (i : d.Idx N) (ω : Ω d)
    (k l : {a : d.Idx N // a ≠ i}) : ‖minorRes d N u z i ω k l‖ ≤ |z.im|⁻¹ :=
  le_trans (norm_apply_le_l2_opNorm _ k l)
    (norm_green_le (isHermitian_Hflow_submatrix d N u ω i) (abs_pos.2 hz) le_rfl)

theorem continuous_minorRes (hz : z.im ≠ 0) (i : d.Idx N) (k l : {a : d.Idx N // a ≠ i}) :
    Continuous fun ω : Ω d => minorRes d N u z i ω k l := by
  refine Continuous.matrix_elem ?_ k l
  exact continuous_green_of_isHermitian
    ((continuous_Hflow d N u).matrix_submatrix _ _)
    (fun ω => isHermitian_Hflow_submatrix d N u ω i) hz

/-- The minor resolvent reads only the off-row block. -/
theorem minorRes_congr (i : d.Idx N) {ω ω' : Ω d}
    (h : ∀ c ∈ offRowCoord d N i, ω c = ω' c) :
    minorRes d N u z i ω = minorRes d N u z i ω' := by
  unfold minorRes
  rw [Hflow_submatrix_congr_offRowCoord u h]

/-! ### The instance -/

/-- **The row chaos of the Gaussian model at row `i`.**  The row is `h_k = (H_u)_{ik}`, the
matrix is the minor resolvent `(H^{(i)} - z)^{-1}`, and the scale is `r = √u`. -/
noncomputable def modelChaos (d : Dims) (N : ℕ) (u : ℝ) {z : ℂ} (hz : z.im ≠ 0)
    (i : d.Idx N) : RowChaos d {a : d.Idx N // a ≠ i} where
  co k b := rowCoord d N i k.1 b
  co_inj := by
    rintro ⟨⟨k, hk⟩, b⟩ ⟨⟨l, hl⟩, c⟩ h
    obtain ⟨h1, h2⟩ := rowCoord_injOn hk hl h
    subst h1; subst h2; rfl
  gvar_tag k := by rw [gvar_rowCoord k.2, gvar_rowCoord k.2]
  eps k := rowSign d N i k.1
  eps_sq k := by unfold rowSign; split_ifs <;> norm_num
  r := Real.sqrt u
  B ω k l := minorRes d N u z i ω k l
  B_cont k l := continuous_minorRes hz i k l
  Bbd := |z.im|⁻¹
  B_bdd ω k l := norm_minorRes_le hz i ω k l
  Ifree := offRowCoord d N i
  Ifree_free k b := by
    intro hmem
    exact (Finset.mem_sdiff.1 hmem).2 (rowCoord_mem_rowSet i k.1 b)
  B_free ω ω' h := by
    funext k l
    rw [minorRes_congr (u := u) (z := z) i h]

/-! ### What the instance is -/

variable (hz : z.im ≠ 0) (i : d.Idx N)

@[simp] theorem modelChaos_B (ω : Ω d) (k l : {a : d.Idx N // a ≠ i}) :
    (modelChaos d N u hz i).B ω k l = minorRes d N u z i ω k l := rfl

@[simp] theorem modelChaos_r : (modelChaos d N u hz i).r = Real.sqrt u := rfl

/-- **The row of the chaos is the `i`-th row of `H_u`.** -/
theorem modelChaos_h (ω : Ω d) (k : {a : d.Idx N // a ≠ i}) :
    (modelChaos d N u hz i).h ω k = Hflow d N u ω i k.1 := by
  show (Real.sqrt u : ℂ) * ((ω (rowCoord d N i k.1 true) : ℂ)
      + ((rowSign d N i k.1 : ℝ) : ℂ) * Complex.I * (ω (rowCoord d N i k.1 false) : ℂ)) = _
  rw [Hflow_apply, Xentry_eq_rowCoord (Ne.symm k.2) ω]

/-- **The variance of the row is `σ_k = u S_{ik}`.** -/
theorem modelChaos_sg (hu : 0 ≤ u) (k : {a : d.Idx N // a ≠ i}) :
    (modelChaos d N u hz i).sg k = u * Sblk (d.L N) (d.W N) i k.1 := by
  show 2 * Real.sqrt u ^ 2 * (gvar d (rowCoord d N i k.1 true) : ℝ) = _
  rw [gvar_rowCoord k.2, Real.sq_sqrt hu]
  ring

/-- **The matrix of the chaos is `G^{(i)}`, for every `ω`.**  The two side conditions of
`RBM.inv_minor_resolvent` hold unconditionally off the real axis. -/
theorem modelChaos_B_eq (ω : Ω d) (k l : {a : d.Idx N // a ≠ i}) :
    (modelChaos d N u hz i).B ω k l
      = greenMinor (green (Hflow d N u ω) z) i k.1 l.1 := by
  show minorRes d N u z i ω k l = _
  unfold minorRes green
  rw [inv_minor_resolvent (isUnit_det_Hflow_sub d N u ω hz)
    i (green_Hflow_diag_ne_zero d N u ω hz i)]
  rfl

/-! ### The two sides of (4.7), in the paper's notation -/

/-- **The chaos of the instance is `ldeQuadLHS`.** -/
theorem modelChaos_normSq_chaos (hu : 0 ≤ u) (ω : Ω d) :
    ‖(modelChaos d N u hz i).chaos ω‖ ^ 2
      = ldeQuadLHS (Hflow d N u ω) (green (Hflow d N u ω) z) (Sblk (d.L N) (d.W N)) u i :=
  RowChaos.norm_chaos_sq_eq_ldeQuadLHS (modelChaos d N u hz i) ω
    (Hflow d N u ω) (green (Hflow d N u ω) z) (Sblk (d.L N) (d.W N)) u
    (fun k => modelChaos_h hz i ω k)
    (fun k => by
      rw [modelChaos_h hz i ω k]
      exact (Hflow_isHermitian d N u ω).apply k.1 i)
    (fun k l => modelChaos_B_eq hz i ω k l)
    (fun k => modelChaos_sg hz i hu k)

/-- **The control of the instance is `u² · ldeQuadRHS`.**  The factor `u²` is the one recorded
in `docs/paper-deltas.md` #59: `E|H_{ik}|² = u S_{ik}` while `ldeQuadRHS` is written with `S`. -/
theorem modelChaos_Vq (hu : 0 ≤ u) (ω : Ω d) :
    (modelChaos d N u hz i).Vq ω
      = u ^ 2 * ldeQuadRHS (Sblk (d.L N) (d.W N)) (green (Hflow d N u ω) z) i :=
  RowChaos.Vq_eq_ldeQuadRHS (modelChaos d N u hz i) ω
    (green (Hflow d N u ω) z) (Sblk (d.L N) (d.W N)) u
    (fun k l => modelChaos_B_eq hz i ω k l)
    (fun k => modelChaos_sg hz i hu k)
    (fun k => by rw [modelChaos_sg hz i hu k, Sblk_comm])

include hz in
/-- **The quadratic large deviation estimate for the Gaussian model, all moments.**

`E[(ldeQuadLHS)^p] ≤ ((2p−1)(4p−2))^p · u^{2p} · E[(ldeQuadRHS)^p]`

for every `p ≥ 1`, with no side conditions beyond `0 ≤ u` and `Im z ≠ 0`.  This is
`RBM.Gauss.RowChaos.mom_le_momVpow` (T93) read through the instance. -/
theorem integral_ldeQuadLHS_pow_le (hG : GaussIBP d) (hu : 0 ≤ u) (q : ℕ) :
    ∫ ω, ldeQuadLHS (Hflow d N u ω) (green (Hflow d N u ω) z)
        (Sblk (d.L N) (d.W N)) u i ^ (q + 1) ∂(P d)
      ≤ ((2 * (q : ℝ) + 1) * (4 * (q : ℝ) + 2)) ^ (q + 1) * (u ^ 2) ^ (q + 1) *
        ∫ ω, ldeQuadRHS (Sblk (d.L N) (d.W N)) (green (Hflow d N u ω) z) i ^ (q + 1) ∂(P d) := by
  set C := modelChaos d N u hz i with hC
  have hmom : C.mom (q + 1)
      = ∫ ω, ldeQuadLHS (Hflow d N u ω) (green (Hflow d N u ω) z)
          (Sblk (d.L N) (d.W N)) u i ^ (q + 1) ∂(P d) := by
    show (∫ ω, ‖C.chaos ω‖ ^ (2 * (q + 1)) ∂(P d)) = _
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    show ‖C.chaos ω‖ ^ (2 * (q + 1))
      = ldeQuadLHS (Hflow d N u ω) (green (Hflow d N u ω) z)
          (Sblk (d.L N) (d.W N)) u i ^ (q + 1)
    rw [pow_mul, modelChaos_normSq_chaos hz i hu ω]
  have hV : C.momVpow (q + 1)
      = (u ^ 2) ^ (q + 1) *
        ∫ ω, ldeQuadRHS (Sblk (d.L N) (d.W N)) (green (Hflow d N u ω) z) i ^ (q + 1) ∂(P d) := by
    show (∫ ω, C.Vq ω ^ (q + 1) ∂(P d)) = _
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    show C.Vq ω ^ (q + 1)
      = (u ^ 2) ^ (q + 1) *
        ldeQuadRHS (Sblk (d.L N) (d.W N)) (green (Hflow d N u ω) z) i ^ (q + 1)
    rw [modelChaos_Vq hz i hu ω, mul_pow]
  have h := C.mom_le_momVpow hG q
  rw [hmom, hV] at h
  calc ∫ ω, ldeQuadLHS (Hflow d N u ω) (green (Hflow d N u ω) z)
        (Sblk (d.L N) (d.W N)) u i ^ (q + 1) ∂(P d)
      ≤ ((2 * (q : ℝ) + 1) * (4 * (q : ℝ) + 2)) ^ (q + 1) *
        ((u ^ 2) ^ (q + 1) *
          ∫ ω, ldeQuadRHS (Sblk (d.L N) (d.W N)) (green (Hflow d N u ω) z) i ^ (q + 1)
            ∂(P d)) := h
    _ = _ := by ring

end RBM.Gauss
