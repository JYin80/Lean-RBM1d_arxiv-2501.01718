/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellBlockNet
import RBM1D.Gauss.APrimeFirstCellJGAllTime
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Moments.SubGaussian

/-!
# Fixed-vector Gaussian block bilinear tail (T420)

This file proves the scalar tail used before the finite-net union.  It concerns one fixed ordered
pair of distinct adjacent blocks and does not make any independence assertion about the opposite
orientation of that pair.
-/

namespace RBM.APrimeFirstCellBlockScalarTail

open Filter Real MeasureTheory ProbabilityTheory Matrix Gauss
open scoped NNReal ENNReal Matrix.Norms.L2Operator ComplexConjugate

noncomputable section

private noncomputable abbrev d : Gauss.Dims := Gauss.Dims.exampleGrow

/-! ## Independent Gaussian coordinates -/

/-- Every coordinate of the actual product model is sub-Gaussian with its literal variance. -/
theorem hasSubgaussianMGF_coord (c : Gauss.Coord d) :
    HasSubgaussianMGF (fun ω : Gauss.Ω d => ω c) (Gauss.gvar d c) (Gauss.P d) := by
  have hLaw : HasLaw (fun ω : Gauss.Ω d => ω c)
      (gaussianReal 0 (Gauss.gvar d c)) (Gauss.P d) :=
    ⟨(measurable_pi_apply c).aemeasurable, Gauss.P_map_eval d c⟩
  constructor
  · intro t
    simpa [Function.comp_def] using
      hLaw.integrable_comp (integrable_exp_mul_gaussianReal (μ := 0) (v := Gauss.gvar d c) t)
  · intro t
    rw [mgf_gaussianReal hLaw]
    simp

/-- The coordinate evaluations in the actual infinite product model are mutually independent. -/
theorem iIndepFun_coord :
    iIndepFun (fun c : Gauss.Coord d => fun ω : Gauss.Ω d => ω c) (Gauss.P d) := by
  unfold Gauss.P
  simpa only [id_eq] using
    (iIndepFun_infinitePi
      (P := fun c : Gauss.Coord d => gaussianReal 0 (Gauss.gvar d c))
      (X := fun _ : Gauss.Coord d => id) (fun _ => measurable_id))

/-- An injectively indexed weighted coordinate sum has the variance proxy obtained by summing
the literal coordinate variances.  This is a genuine model-law statement, not an independence
hypothesis. -/
theorem hasSubgaussianMGF_weighted_coord_sum
    {ι : Type*} [Fintype ι]
    (c : ι → Gauss.Coord d) (hc : Function.Injective c) (a : ι → ℝ) :
    HasSubgaussianMGF
      (fun ω : Gauss.Ω d => ∑ i : ι, a i * ω (c i))
      (∑ i : ι, ⟨(a i) ^ 2, sq_nonneg (a i)⟩ * Gauss.gvar d (c i)) (Gauss.P d) := by
  classical
  have hi : iIndepFun (fun i : ι => fun ω : Gauss.Ω d => ω (c i)) (Gauss.P d) :=
    iIndepFun_coord.precomp hc
  have his : iIndepFun
      (fun i : ι => (fun x : ℝ => a i * x) ∘ fun ω : Gauss.Ω d => ω (c i)) (Gauss.P d) :=
    hi.comp (fun i x => a i * x) (fun _ => by fun_prop)
  simpa only [Function.comp_apply, Finset.mem_univ, forall_const, Finset.sum_filter,
    Finset.filter_true_of_mem] using
    HasSubgaussianMGF.sum_of_iIndepFun his (s := Finset.univ)
      (fun i _ => (hasSubgaussianMGF_coord (c i)).const_mul (a i))

/-! ## Coordinates of one ordered off-diagonal block -/

private theorem block_val_lt_or_gt (N : ℕ) {x y : ZMod (d.L N)} (hxy : x ≠ y) :
    x.val < y.val ∨ y.val < x.val := by
  rcases lt_trichotomy x.val y.val with h | h | h
  · exact Or.inl h
  · exact absurd (ZMod.val_injective _ h) hxy
  · exact Or.inr h

private theorem eq_zero_or_eq_one_or_eq_neg_one_of_zdist_le_one
    (L : ℕ) [NeZero L] (hL : 3 ≤ L) (u : ZMod L)
    (hu : zdist L u ≤ 1) : u = 0 ∨ u = 1 ∨ u = -1 := by
  have hval : u.val ≤ 1 ∨ L - u.val ≤ 1 := by
    simpa only [zdist, min_le_iff] using hu
  rcases hval with hval | hval
  · have huv : u.val = 0 ∨ u.val = 1 := by omega
    rcases huv with huv | huv
    · left
      apply ZMod.val_injective L
      simpa using huv
    · right; left
      apply ZMod.val_injective L
      simpa [val_one_eq L hL] using huv
  · have huval : u.val < L := ZMod.val_lt u
    have huv : u.val = L - 1 := by omega
    right; right
    apply ZMod.val_injective L
    simpa [val_neg_one_eq L hL] using huv

private theorem mem_sbSupport_of_adjacent (N : ℕ) {x y : ZMod (d.L N)}
    (hxy : x ≠ y) (hadj : zdist (d.L N) (x - y) ≤ 1) :
    x - y ∈ sbSupport (d.L N) := by
  rcases eq_zero_or_eq_one_or_eq_neg_one_of_zdist_le_one
    (d.L N) (d.three_le_L N) (x - y) hadj with h | h | h
  · exact absurd (sub_eq_zero.mp h) hxy
  · rw [h]
    simp only [sbSupport, Finset.mem_insert, Finset.mem_singleton]
    exact Or.inr (Or.inl trivial)
  · rw [h]
    simp only [sbSupport, Finset.mem_insert, Finset.mem_singleton]
    exact Or.inr (Or.inr trivial)

private theorem idxKey_lt_of_block_val_lt (N : ℕ) {x y : ZMod (d.L N)}
    (hxy : x.val < y.val) (p q : Fin (d.W N)) :
    Gauss.idxKey d N (x, p) < Gauss.idxKey d N (y, q) := by
  simp only [Gauss.idxKey]
  have hp := p.isLt
  have hq : 0 ≤ (q : ℕ) := Nat.zero_le _
  have hW := d.W_pos N
  change d.W N * x.val + (p : ℕ) < d.W N * y.val + (q : ℕ)
  calc
    d.W N * x.val + (p : ℕ) < d.W N * x.val + d.W N :=
      Nat.add_lt_add_left p.isLt _
    _ = d.W N * (x.val + 1) := by ring
    _ ≤ d.W N * y.val := Nat.mul_le_mul_left _ (Nat.succ_le_iff.mpr hxy)
    _ ≤ d.W N * y.val + (q : ℕ) := Nat.le_add_right _ _

/-- The sign of the imaginary coordinate in the ordered entry `X_{(x,p),(y,q)}`. -/
def blockSign (N : ℕ) (x y : ZMod (d.L N)) : ℝ := if x.val < y.val then 1 else -1

/-- The underlying product coordinate for an entry of the ordered block `(x,y)`. -/
def blockCoord (N : ℕ) (x y : ZMod (d.L N))
    (i : Fin (d.W N) × Fin (d.W N) × Bool) : Gauss.Coord d :=
  if x.val < y.val then ⟨N, (x, i.1), (y, i.2.1), i.2.2⟩
  else ⟨N, (y, i.2.1), (x, i.1), i.2.2⟩

theorem blockCoord_injective (N : ℕ) {x y : ZMod (d.L N)} :
    Function.Injective (blockCoord N x y) := by
  intro i j hij
  unfold blockCoord at hij
  split_ifs at hij
  · apply Prod.ext
    · apply Fin.ext
      exact congrArg (fun c : Gauss.Coord d => c.2.1.2.val) hij
    · apply Prod.ext
      · apply Fin.ext
        exact congrArg (fun c : Gauss.Coord d => c.2.2.1.2.val) hij
      · exact congrArg (fun c : Gauss.Coord d => c.2.2.2) hij
  · apply Prod.ext
    · apply Fin.ext
      exact congrArg (fun c : Gauss.Coord d => c.2.2.1.2.val) hij
    · apply Prod.ext
      · apply Fin.ext
        exact congrArg (fun c : Gauss.Coord d => c.2.1.2.val) hij
      · exact congrArg (fun c : Gauss.Coord d => c.2.2.2) hij

theorem gvar_blockCoord (N : ℕ) {x y : ZMod (d.L N)}
    (hxy : x ≠ y) (hadj : zdist (d.L N) (x - y) ≤ 1)
    (i : Fin (d.W N) × Fin (d.W N) × Bool) :
    (Gauss.gvar d (blockCoord N x y i) : ℝ) = 1 / (6 * (d.W N : ℝ)) := by
  have hW : (d.W N : ℝ) ≠ 0 := by exact_mod_cast (d.W_pos N).ne'
  by_cases hval : x.val < y.val
  · rw [blockCoord, ite_eq_left hval]
    rw [Gauss.gvar_offDiag d N (x, i.1) (y, i.2.1) i.2.2 (by
      intro h
      exact hxy (congrArg Prod.fst h))]
    rw [Sblk, sbKre, ite_eq_left (mem_sbSupport_of_adjacent N hxy hadj)]
    field_simp
    norm_num
  · have hrev : zdist (d.L N) (y - x) ≤ 1 := by
      rw [show y - x = -(x - y) by ring, zdist_neg]
      exact hadj
    rw [blockCoord, ite_eq_right hval]
    rw [Gauss.gvar_offDiag d N (y, i.2.1) (x, i.1) i.2.2 (by
      intro h
      exact hxy (congrArg Prod.fst h).symm)]
    rw [Sblk, sbKre, ite_eq_left (mem_sbSupport_of_adjacent N hxy.symm hrev)]
    field_simp
    norm_num

/-- The complex coefficient `conj(v_p) w_q`. -/
def blockCoeff (N : ℕ) (v w : Gauss.BlockVec (d.W N))
    (p q : Fin (d.W N)) : ℂ := (starRingEnd ℂ) (v.ofLp p) * w.ofLp q

/-- Coefficients of the real part of the ordered block bilinear form. -/
def blockReCoeff (N : ℕ) (x y : ZMod (d.L N))
    (v w : Gauss.BlockVec (d.W N))
    (i : Fin (d.W N) × Fin (d.W N) × Bool) : ℝ :=
  if i.2.2 then (blockCoeff N v w i.1 i.2.1).re
  else -(blockSign N x y) * (blockCoeff N v w i.1 i.2.1).im

/-- Coefficients of the imaginary part of the ordered block bilinear form. -/
def blockImCoeff (N : ℕ) (x y : ZMod (d.L N))
    (v w : Gauss.BlockVec (d.W N))
    (i : Fin (d.W N) × Fin (d.W N) × Bool) : ℝ :=
  if i.2.2 then (blockCoeff N v w i.1 i.2.1).im
  else blockSign N x y * (blockCoeff N v w i.1 i.2.1).re

theorem blockSign_sq (N : ℕ) (x y : ZMod (d.L N)) : (blockSign N x y) ^ 2 = 1 := by
  unfold blockSign
  split_ifs <;> norm_num

private theorem sum_bool_blockReCoeff_sq (N : ℕ) (x y : ZMod (d.L N))
    (v w : Gauss.BlockVec (d.W N)) (p q : Fin (d.W N)) :
    ∑ b : Bool, (blockReCoeff N x y v w (p, q, b)) ^ 2 = ‖blockCoeff N v w p q‖ ^ 2 := by
  rw [Fintype.sum_bool]
  change (blockCoeff N v w p q).re ^ 2 +
      (-(blockSign N x y) * (blockCoeff N v w p q).im) ^ 2 = _
  rw [neg_mul, neg_sq, mul_pow, blockSign_sq, one_mul]
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  ring

private theorem sum_bool_blockImCoeff_sq (N : ℕ) (x y : ZMod (d.L N))
    (v w : Gauss.BlockVec (d.W N)) (p q : Fin (d.W N)) :
    ∑ b : Bool, (blockImCoeff N x y v w (p, q, b)) ^ 2 = ‖blockCoeff N v w p q‖ ^ 2 := by
  rw [Fintype.sum_bool]
  change (blockCoeff N v w p q).im ^ 2 +
      (blockSign N x y * (blockCoeff N v w p q).re) ^ 2 = _
  rw [mul_pow, blockSign_sq, one_mul]
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  ring

private theorem sum_norm_blockCoeff_sq (N : ℕ)
    {v w : Gauss.BlockVec (d.W N)} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    ∑ p : Fin (d.W N), ∑ q : Fin (d.W N), ‖blockCoeff N v w p q‖ ^ 2 = 1 := by
  have hvsum : ∑ p : Fin (d.W N), ‖v.ofLp p‖ ^ 2 = 1 := by
    rw [← EuclideanSpace.norm_sq_eq, hv]
    norm_num
  have hwsum : ∑ q : Fin (d.W N), ‖w.ofLp q‖ ^ 2 = 1 := by
    rw [← EuclideanSpace.norm_sq_eq, hw]
    norm_num
  simp only [blockCoeff, norm_mul, Complex.norm_conj, mul_pow]
  calc
    ∑ p : Fin (d.W N), ∑ q : Fin (d.W N), ‖v.ofLp p‖ ^ 2 * ‖w.ofLp q‖ ^ 2 =
        ∑ p : Fin (d.W N), ‖v.ofLp p‖ ^ 2 *
          (∑ q : Fin (d.W N), ‖w.ofLp q‖ ^ 2) := by
          apply Finset.sum_congr rfl
          intro p _
          rw [Finset.mul_sum]
    _ = (∑ p : Fin (d.W N), ‖v.ofLp p‖ ^ 2) *
          (∑ q : Fin (d.W N), ‖w.ofLp q‖ ^ 2) := by
          rw [Finset.sum_mul]
    _ = 1 := by rw [hvsum, hwsum, one_mul]

theorem sum_blockReCoeff_sq (N : ℕ) (x y : ZMod (d.L N))
    {v w : Gauss.BlockVec (d.W N)} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    ∑ i : Fin (d.W N) × Fin (d.W N) × Bool, (blockReCoeff N x y v w i) ^ 2 = 1 := by
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type, sum_bool_blockReCoeff_sq]
  exact sum_norm_blockCoeff_sq N hv hw

theorem sum_blockImCoeff_sq (N : ℕ) (x y : ZMod (d.L N))
    {v w : Gauss.BlockVec (d.W N)} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    ∑ i : Fin (d.W N) × Fin (d.W N) × Bool, (blockImCoeff N x y v w i) ^ 2 = 1 := by
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type, sum_bool_blockImCoeff_sq]
  exact sum_norm_blockCoeff_sq N hv hw

/-! ## The actual block bilinear form -/

private theorem Xentry_eq_coord (N : ℕ) (ω : Gauss.Ω d)
    {x y : ZMod (d.L N)} (hxy : x ≠ y) (p q : Fin (d.W N)) :
    Gauss.Xentry d N ω (x, p) (y, q) =
      (ω (blockCoord N x y (p, q, true)) : ℂ) +
        (blockSign N x y : ℂ) * Complex.I *
          (ω (blockCoord N x y (p, q, false)) : ℂ) := by
  by_cases hval : x.val < y.val
  · have hkey := idxKey_lt_of_block_val_lt N hval p q
    rw [Gauss.Xentry, ite_eq_left hkey]
    rw [blockCoord, ite_eq_left hval, blockCoord, ite_eq_left hval,
      blockSign, ite_eq_left hval]
    norm_num
  · have hrev : y.val < x.val := (block_val_lt_or_gt N hxy).resolve_left hval
    have hkey := idxKey_lt_of_block_val_lt N hrev q p
    have hnkey : ¬Gauss.idxKey d N (x, p) < Gauss.idxKey d N (y, q) :=
      not_lt_of_ge hkey.le
    rw [Gauss.Xentry, ite_eq_right hnkey, ite_eq_left hkey]
    rw [blockCoord, ite_eq_right hval, blockCoord, ite_eq_right hval,
      blockSign, ite_eq_right hval]
    norm_num [sub_eq_add_neg]

/-- The fixed-vector scalar observable for one ordered block. -/
noncomputable def blockScalar (N : ℕ) (ω : Gauss.Ω d)
    (x y : ZMod (d.L N)) (v w : Gauss.BlockVec (d.W N)) : ℂ :=
  inner ℂ v
    (Matrix.toEuclideanCLM (n := Fin (d.W N)) (𝕜 := ℂ)
      (APrimeFirstCellJGAllTime.xBlock N ω x y) w)

private theorem blockScalar_eq_sum (N : ℕ) (ω : Gauss.Ω d)
    {x y : ZMod (d.L N)} (hxy : x ≠ y)
    (v w : Gauss.BlockVec (d.W N)) :
    blockScalar N ω x y v w =
      ∑ p : Fin (d.W N), ∑ q : Fin (d.W N),
        blockCoeff N v w p q *
          ((ω (blockCoord N x y (p, q, true)) : ℂ) +
            (blockSign N x y : ℂ) * Complex.I *
              (ω (blockCoord N x y (p, q, false)) : ℂ)) := by
  change inner ℂ v
      (Matrix.toEuclideanCLM (n := Fin (d.W N)) (𝕜 := ℂ)
        (Matrix.of fun p q => Gauss.Xentry d N ω (x, p) (y, q)) w) = _
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct]
  apply Finset.sum_congr rfl
  intro p _
  rw [Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro q _
  change Gauss.Xentry d N ω (x, p) (y, q) * w.ofLp q *
      (starRingEnd ℂ) (v.ofLp p) = _
  rw [Xentry_eq_coord N ω hxy p q]
  simp only [blockCoeff]
  ring

theorem blockScalar_re_eq_coord_sum (N : ℕ) (ω : Gauss.Ω d)
    {x y : ZMod (d.L N)} (hxy : x ≠ y)
    (v w : Gauss.BlockVec (d.W N)) :
    (blockScalar N ω x y v w).re =
      ∑ i : Fin (d.W N) × Fin (d.W N) × Bool,
        blockReCoeff N x y v w i * ω (blockCoord N x y i) := by
  rw [blockScalar_eq_sum N ω hxy v w, Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type, Fintype.sum_bool]
  change Complex.reCLM
      (∑ p : Fin (d.W N), ∑ q : Fin (d.W N),
        blockCoeff N v w p q *
          ((ω (blockCoord N x y (p, q, true)) : ℂ) +
            (blockSign N x y : ℂ) * Complex.I *
              (ω (blockCoord N x y (p, q, false)) : ℂ))) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro q _
  simp [Complex.reCLM_apply, blockReCoeff, blockCoeff]
  ring

theorem blockScalar_im_eq_coord_sum (N : ℕ) (ω : Gauss.Ω d)
    {x y : ZMod (d.L N)} (hxy : x ≠ y)
    (v w : Gauss.BlockVec (d.W N)) :
    (blockScalar N ω x y v w).im =
      ∑ i : Fin (d.W N) × Fin (d.W N) × Bool,
        blockImCoeff N x y v w i * ω (blockCoord N x y i) := by
  rw [blockScalar_eq_sum N ω hxy v w, Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type, Fintype.sum_bool]
  change Complex.imCLM
      (∑ p : Fin (d.W N), ∑ q : Fin (d.W N),
        blockCoeff N v w p q *
          ((ω (blockCoord N x y (p, q, true)) : ℂ) +
            (blockSign N x y : ℂ) * Complex.I *
              (ω (blockCoord N x y (p, q, false)) : ℂ))) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro q _
  simp [Complex.imCLM_apply, blockImCoeff, blockCoeff]
  ring

/-! ## Exact projected variance proxies -/

/-- The real and imaginary projections both have variance proxy `1/(6W)`. -/
noncomputable def blockVarProxy (N : ℕ) : ℝ≥0 :=
  ⟨1 / (6 * (d.W N : ℝ)), by positivity⟩

theorem hasSubgaussianMGF_blockScalar_re (N : ℕ)
    {x y : ZMod (d.L N)} (hxy : x ≠ y)
    (hadj : zdist (d.L N) (x - y) ≤ 1)
    {v w : Gauss.BlockVec (d.W N)} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    HasSubgaussianMGF (fun ω : Gauss.Ω d => (blockScalar N ω x y v w).re)
      (blockVarProxy N) (Gauss.P d) := by
  have hs := hasSubgaussianMGF_weighted_coord_sum
    (blockCoord N x y) (blockCoord_injective N)
    (blockReCoeff N x y v w)
  have hproxy :
      (∑ i : Fin (d.W N) × Fin (d.W N) × Bool,
        NNReal.mk ((blockReCoeff N x y v w i) ^ 2)
          (sq_nonneg (blockReCoeff N x y v w i)) *
            Gauss.gvar d (blockCoord N x y i)) = blockVarProxy N := by
    apply NNReal.eq
    simp only [NNReal.coe_sum, NNReal.coe_mul, NNReal.coe_mk, blockVarProxy]
    simp_rw [gvar_blockCoord N hxy hadj]
    rw [← Finset.sum_mul, sum_blockReCoeff_sq N x y hv hw, one_mul]
    rfl
  have hs' :
      HasSubgaussianMGF
        (fun ω : Gauss.Ω d => ∑ i, blockReCoeff N x y v w i * ω (blockCoord N x y i))
        (∑ i, NNReal.mk ((blockReCoeff N x y v w i) ^ 2)
          (sq_nonneg (blockReCoeff N x y v w i)) * Gauss.gvar d (blockCoord N x y i))
        (Gauss.P d) := by
    simpa only [NNReal.mk] using hs
  rw [hproxy] at hs'
  exact hs'.congr (Filter.Eventually.of_forall fun ω =>
    (blockScalar_re_eq_coord_sum N ω hxy v w).symm)

theorem hasSubgaussianMGF_blockScalar_im (N : ℕ)
    {x y : ZMod (d.L N)} (hxy : x ≠ y)
    (hadj : zdist (d.L N) (x - y) ≤ 1)
    {v w : Gauss.BlockVec (d.W N)} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    HasSubgaussianMGF (fun ω : Gauss.Ω d => (blockScalar N ω x y v w).im)
      (blockVarProxy N) (Gauss.P d) := by
  have hs := hasSubgaussianMGF_weighted_coord_sum
    (blockCoord N x y) (blockCoord_injective N)
    (blockImCoeff N x y v w)
  have hproxy :
      (∑ i : Fin (d.W N) × Fin (d.W N) × Bool,
        NNReal.mk ((blockImCoeff N x y v w i) ^ 2)
          (sq_nonneg (blockImCoeff N x y v w i)) *
            Gauss.gvar d (blockCoord N x y i)) = blockVarProxy N := by
    apply NNReal.eq
    simp only [NNReal.coe_sum, NNReal.coe_mul, NNReal.coe_mk, blockVarProxy]
    simp_rw [gvar_blockCoord N hxy hadj]
    rw [← Finset.sum_mul, sum_blockImCoeff_sq N x y hv hw, one_mul]
    rfl
  have hs' :
      HasSubgaussianMGF
        (fun ω : Gauss.Ω d => ∑ i, blockImCoeff N x y v w i * ω (blockCoord N x y i))
        (∑ i, NNReal.mk ((blockImCoeff N x y v w i) ^ 2)
          (sq_nonneg (blockImCoeff N x y v w i)) * Gauss.gvar d (blockCoord N x y i))
        (Gauss.P d) := by
    simpa only [NNReal.mk] using hs
  rw [hproxy] at hs'
  exact hs'.congr (Filter.Eventually.of_forall fun ω =>
    (blockScalar_im_eq_coord_sum N ω hxy v w).symm)

/-! ## One-dimensional and four-tail estimates -/

private theorem projected_upper_tail (N : ℕ) {X : Gauss.Ω d → ℝ}
    (hX : HasSubgaussianMGF X (blockVarProxy N) (Gauss.P d))
    {s : ℝ} (hs : 0 ≤ s) :
    (Gauss.P d).real {ω | s ≤ X ω} ≤
      Real.exp (-3 * (d.W N : ℝ) * s ^ 2) := by
  have h := hX.measure_ge_le hs
  calc
    (Gauss.P d).real {ω | s ≤ X ω} ≤
        Real.exp (-s ^ 2 / (2 * (blockVarProxy N : ℝ))) := h
    _ = Real.exp (-3 * (d.W N : ℝ) * s ^ 2) := by
      congr 1
      have hW : (d.W N : ℝ) ≠ 0 := by exact_mod_cast (d.W_pos N).ne'
      change -s ^ 2 / (2 * (1 / (6 * (d.W N : ℝ)))) = _
      field_simp [hW]
      ring

private theorem projected_lower_tail (N : ℕ) {X : Gauss.Ω d → ℝ}
    (hX : HasSubgaussianMGF X (blockVarProxy N) (Gauss.P d))
    {s : ℝ} (hs : 0 ≤ s) :
    (Gauss.P d).real {ω | s ≤ -X ω} ≤
      Real.exp (-3 * (d.W N : ℝ) * s ^ 2) := by
  simpa only [Pi.neg_apply] using projected_upper_tail N hX.neg hs

theorem blockScalar_norm_tail (N : ℕ)
    {x y : ZMod (d.L N)} (hxy : x ≠ y)
    (hadj : zdist (d.L N) (x - y) ≤ 1)
    {v w : Gauss.BlockVec (d.W N)} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    {r : ℝ} (hr : 0 ≤ r) :
    (Gauss.P d).real {ω | r < ‖blockScalar N ω x y v w‖} ≤
      4 * Real.exp (-(3 / 2 : ℝ) * (d.W N : ℝ) * r ^ 2) := by
  let s : ℝ := r / Real.sqrt 2
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hs : 0 ≤ s := div_nonneg hr hsqrt.le
  have hscale : 2 * s ^ 2 = r ^ 2 := by
    dsimp [s]
    rw [div_pow]
    field_simp [ne_of_gt hsqrt]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  let A : Set (Gauss.Ω d) := {ω | s ≤ (blockScalar N ω x y v w).re}
  let B : Set (Gauss.Ω d) := {ω | s ≤ -(blockScalar N ω x y v w).re}
  let C : Set (Gauss.Ω d) := {ω | s ≤ (blockScalar N ω x y v w).im}
  let D : Set (Gauss.Ω d) := {ω | s ≤ -(blockScalar N ω x y v w).im}
  have hsub : {ω | r < ‖blockScalar N ω x y v w‖} ⊆ (A ∪ B) ∪ (C ∪ D) := by
    intro ω hω
    change r < ‖blockScalar N ω x y v w‖ at hω
    by_cases hA : s ≤ (blockScalar N ω x y v w).re
    · exact Or.inl (Or.inl hA)
    by_cases hB : s ≤ -(blockScalar N ω x y v w).re
    · exact Or.inl (Or.inr hB)
    by_cases hC : s ≤ (blockScalar N ω x y v w).im
    · exact Or.inr (Or.inl hC)
    by_cases hD : s ≤ -(blockScalar N ω x y v w).im
    · exact Or.inr (Or.inr hD)
    exfalso
    have hre_hi : (blockScalar N ω x y v w).re < s := lt_of_not_ge hA
    have hre_lo : -s < (blockScalar N ω x y v w).re := by linarith
    have him_hi : (blockScalar N ω x y v w).im < s := lt_of_not_ge hC
    have him_lo : -s < (blockScalar N ω x y v w).im := by linarith
    have hre_sq : (blockScalar N ω x y v w).re ^ 2 < s ^ 2 := by
      have hp : 0 < (s - (blockScalar N ω x y v w).re) *
          (s + (blockScalar N ω x y v w).re) :=
        mul_pos (sub_pos.mpr hre_hi) (by linarith)
      nlinarith
    have him_sq : (blockScalar N ω x y v w).im ^ 2 < s ^ 2 := by
      have hp : 0 < (s - (blockScalar N ω x y v w).im) *
          (s + (blockScalar N ω x y v w).im) :=
        mul_pos (sub_pos.mpr him_hi) (by linarith)
      nlinarith
    have hnormsq : ‖blockScalar N ω x y v w‖ ^ 2 =
        (blockScalar N ω x y v w).re ^ 2 +
          (blockScalar N ω x y v w).im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    nlinarith [norm_nonneg (blockScalar N ω x y v w)]
  have hre := hasSubgaussianMGF_blockScalar_re N hxy hadj hv hw
  have him := hasSubgaussianMGF_blockScalar_im N hxy hadj hv hw
  have hA : (Gauss.P d).real A ≤ Real.exp (-3 * (d.W N : ℝ) * s ^ 2) := by
    exact projected_upper_tail N hre hs
  have hB : (Gauss.P d).real B ≤ Real.exp (-3 * (d.W N : ℝ) * s ^ 2) := by
    exact projected_lower_tail N hre hs
  have hC : (Gauss.P d).real C ≤ Real.exp (-3 * (d.W N : ℝ) * s ^ 2) := by
    exact projected_upper_tail N him hs
  have hD : (Gauss.P d).real D ≤ Real.exp (-3 * (d.W N : ℝ) * s ^ 2) := by
    exact projected_lower_tail N him hs
  calc
    (Gauss.P d).real {ω | r < ‖blockScalar N ω x y v w‖} ≤
        (Gauss.P d).real ((A ∪ B) ∪ (C ∪ D)) :=
      measureReal_mono hsub
    _ ≤ (Gauss.P d).real (A ∪ B) + (Gauss.P d).real (C ∪ D) :=
      measureReal_union_le _ _
    _ ≤ ((Gauss.P d).real A + (Gauss.P d).real B) +
        ((Gauss.P d).real C + (Gauss.P d).real D) :=
      add_le_add (measureReal_union_le _ _) (measureReal_union_le _ _)
    _ ≤ 4 * Real.exp (-3 * (d.W N : ℝ) * s ^ 2) := by linarith
    _ = 4 * Real.exp (-(3 / 2 : ℝ) * (d.W N : ℝ) * r ^ 2) := by
      congr 2
      rw [show r ^ 2 = 2 * s ^ 2 by linarith [hscale]]
      ring

/-- Fixed-vector tail for the actual ordered block of the `exampleGrow` Gaussian law. -/
theorem fixed_block_bilinear_tail (N : ℕ)
    {x y : ZMod (d.L N)} (hxy : x ≠ y)
    (hadj : zdist (d.L N) (x - y) ≤ 1)
    {v w : Gauss.BlockVec (d.W N)} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    {r : ℝ} (hr : 0 ≤ r) :
    (Gauss.P d).real
        {ω | r < ‖inner ℂ v
          (Matrix.toEuclideanCLM (n := Fin (d.W N)) (𝕜 := ℂ)
            (APrimeFirstCellJGAllTime.xBlock N ω x y) w)‖} ≤
      4 * Real.exp (-(3 / 2 : ℝ) * (d.W N : ℝ) * r ^ 2) := by
  change (Gauss.P d).real {ω | r < ‖blockScalar N ω x y v w‖} ≤ _
  exact blockScalar_norm_tail N hxy hadj hv hw hr

/-- The threshold endpoint `r = 0` is covered without dividing by `r`. -/
theorem fixed_block_bilinear_tail_zero (N : ℕ)
    {x y : ZMod (d.L N)} (hxy : x ≠ y)
    (hadj : zdist (d.L N) (x - y) ≤ 1)
    {v w : Gauss.BlockVec (d.W N)} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    (Gauss.P d).real
        {ω | 0 < ‖inner ℂ v
          (Matrix.toEuclideanCLM (n := Fin (d.W N)) (𝕜 := ℂ)
            (APrimeFirstCellJGAllTime.xBlock N ω x y) w)‖} ≤ 4 := by
  simpa using fixed_block_bilinear_tail N hxy hadj hv hw (r := 0) (by norm_num)

/-- The tail constant specializes correctly at the bandwidth endpoint `W = 1`. -/
theorem fixed_block_bilinear_tail_width_one (N : ℕ) (hW : d.W N = 1)
    {x y : ZMod (d.L N)} (hxy : x ≠ y)
    (hadj : zdist (d.L N) (x - y) ≤ 1)
    {v w : Gauss.BlockVec (d.W N)} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    {r : ℝ} (hr : 0 ≤ r) :
    (Gauss.P d).real
        {ω | r < ‖inner ℂ v
          (Matrix.toEuclideanCLM (n := Fin (d.W N)) (𝕜 := ℂ)
            (APrimeFirstCellJGAllTime.xBlock N ω x y) w)‖} ≤
      4 * Real.exp (-(3 / 2 : ℝ) * r ^ 2) := by
  have hWr : (d.W N : ℝ) = 1 := by exact_mod_cast hW
  calc
    (Gauss.P d).real
        {ω | r < ‖inner ℂ v
          (Matrix.toEuclideanCLM (n := Fin (d.W N)) (𝕜 := ℂ)
            (APrimeFirstCellJGAllTime.xBlock N ω x y) w)‖} ≤
        4 * Real.exp (-(3 / 2 : ℝ) * (d.W N : ℝ) * r ^ 2) :=
      fixed_block_bilinear_tail N hxy hadj hv hw hr
    _ = 4 * Real.exp (-(3 / 2 : ℝ) * r ^ 2) := by rw [hWr]; ring

/-- The concrete `exampleGrow` law actually realizes the endpoint `W = 1` at `N = 0`. -/
theorem exampleGrow_width_zero : d.W 0 = 1 := by
  change Gauss.Dims.growW 0 = 1
  norm_num [Gauss.Dims.growW, Gauss.Dims.growL]

#print axioms hasSubgaussianMGF_coord
#print axioms iIndepFun_coord
#print axioms hasSubgaussianMGF_weighted_coord_sum
#print axioms hasSubgaussianMGF_blockScalar_re
#print axioms hasSubgaussianMGF_blockScalar_im
#print axioms fixed_block_bilinear_tail
#print axioms fixed_block_bilinear_tail_zero
#print axioms fixed_block_bilinear_tail_width_one
#print axioms exampleGrow_width_zero

end

end RBM.APrimeFirstCellBlockScalarTail
