/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellJGAllTime

/-!
# T414: deterministic cyclic block Combes--Thomas decay

This file formalizes the deterministic first-cell Combes--Thomas argument,
including the cyclic two-neighbour block estimate and the terminal `jG` bound.
-/

namespace RBM.APrimeFirstCellCTDecay

open Filter Real Gauss Matrix
open scoped Matrix.Norms.L2Operator

private noncomputable abbrev d : Gauss.Dims := Gauss.Dims.exampleGrow
private noncomputable abbrev B : Band (Gauss.Ω d) := Gauss.band d

theorem eq_zero_or_eq_one_or_eq_neg_one_of_zdist_le_one
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

noncomputable def weightVal (N : ℕ) (b x : ZMod (B.L N)) : ℝ :=
  Real.exp (APrimeFirstCellJGAllTime.ctAlpha * (zdist (B.L N) (x - b) : ℝ))

noncomputable def weightMat (N : ℕ) (b : ZMod (B.L N)) :
    Matrix (B.Idx N) (B.Idx N) ℂ :=
  Matrix.diagonal fun i => (weightVal N b i.1 : ℂ)

noncomputable def weightInvMat (N : ℕ) (b : ZMod (B.L N)) :
    Matrix (B.Idx N) (B.Idx N) ℂ :=
  Matrix.diagonal fun i =>
    (Real.exp (-APrimeFirstCellJGAllTime.ctAlpha *
      (zdist (B.L N) (i.1 - b) : ℝ)) : ℂ)

theorem abs_weight_ratio_sub_one_le
    (N : ℕ) (b x y : ZMod (B.L N))
    (hxy : zdist (B.L N) (x - y) ≤ 1) :
    |Real.exp (APrimeFirstCellJGAllTime.ctAlpha *
        ((zdist (B.L N) (x - b) : ℝ) - (zdist (B.L N) (y - b) : ℝ))) - 1| ≤
      1 / 64 := by
  let α := APrimeFirstCellJGAllTime.ctAlpha
  let dx : ℝ := zdist (B.L N) (x - b)
  let dy : ℝ := zdist (B.L N) (y - b)
  have hxy' : (zdist (B.L N) (x - y) : ℝ) ≤ 1 := by exact_mod_cast hxy
  have h₁ := zdist_sub_le_add (B.L N) x b y
  have h₂ := zdist_sub_le_add (B.L N) y b x
  rw [Lemma57.zdist_sub_comm (B.L N) b y] at h₁
  rw [Lemma57.zdist_sub_comm (B.L N) b x,
    Lemma57.zdist_sub_comm (B.L N) y x] at h₂
  have hdx : dx ≤ 1 + dy := by
    dsimp only [dx, dy]
    linarith
  have hdy : dy ≤ 1 + dx := by
    dsimp only [dx, dy]
    linarith
  have hα : 0 < α := APrimeFirstCellJGAllTime.ctAlpha_pos
  have ht : |α * (dx - dy)| ≤ α := by
    rw [abs_mul, abs_of_pos hα]
    have : |dx - dy| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
    nlinarith
  have hexp : Real.exp α = 65 / 64 := by
    rw [show α = Real.log (65 / 64 : ℝ) by rfl, Real.exp_log (by norm_num)]
  have hexpn : Real.exp (-α) = 64 / 65 := by
    rw [Real.exp_neg, hexp]
    norm_num
  let t := α * (dx - dy)
  have ht' : -α ≤ t ∧ t ≤ α := abs_le.1 ht
  by_cases ht0 : 0 ≤ t
  · rw [abs_of_nonneg (sub_nonneg.mpr (Real.one_le_exp ht0))]
    have he := Real.exp_le_exp.mpr ht'.2
    rw [hexp] at he
    norm_num at he ⊢
    linarith
  · have htneg : t < 0 := lt_of_not_ge ht0
    rw [abs_of_nonpos (sub_nonpos.mpr (Real.exp_le_one_iff.mpr htneg.le))]
    have he := Real.exp_le_exp.mpr ht'.1
    rw [hexpn] at he
    norm_num at he ⊢
    linarith

theorem weight_mul_inv (N : ℕ) (b : ZMod (B.L N)) :
    weightMat N b * weightInvMat N b = 1 := by
  rw [weightMat, weightInvMat, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    rw [weightVal]
    norm_cast
    rw [← Real.exp_add]
    norm_num
  · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply, hij]

theorem inv_mul_weight (N : ℕ) (b : ZMod (B.L N)) :
    weightInvMat N b * weightMat N b = 1 := by
  rw [weightMat, weightInvMat, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    rw [weightVal]
    norm_cast
    rw [← Real.exp_add]
    norm_num
  · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply, hij]

noncomputable def conjPerturb (N : ℕ) (u : ℝ) (ω : Gauss.Ω d)
    (b : ZMod (B.L N)) : Matrix (B.Idx N) (B.Idx N) ℂ :=
  weightMat N b * (Gauss.sample d).H N u ω * weightInvMat N b -
    (Gauss.sample d).H N u ω

noncomputable def perturbBlock (N : ℕ) (u : ℝ) (ω : Gauss.Ω d)
    (b x y : ZMod (B.L N)) : Matrix (Fin (B.W N)) (Fin (B.W N)) ℂ :=
  fun p q => conjPerturb N u ω b (x, p) (y, q)

theorem perturbBlock_eq_smul (N : ℕ) (u : ℝ) (ω : Gauss.Ω d)
    (b x y : ZMod (B.L N)) :
    perturbBlock N u ω b x y =
      ((Real.sqrt u *
        (Real.exp (APrimeFirstCellJGAllTime.ctAlpha *
          ((zdist (B.L N) (x - b) : ℝ) - (zdist (B.L N) (y - b) : ℝ))) - 1) : ℝ) : ℂ) •
        APrimeFirstCellJGAllTime.xBlock N ω x y := by
  ext p q
  have hHentry : (Gauss.sample d).H N u ω (x, p) (y, q) =
      ((Real.sqrt u : ℝ) : ℂ) *
        APrimeFirstCellJGAllTime.xBlock N ω x y p q := by
    change Hflow d N u ω (x, p) (y, q) = _
    simp only [Hflow, Matrix.smul_apply, smul_eq_mul,
      APrimeFirstCellJGAllTime.xBlock, Xmat_apply]
  simp only [perturbBlock, conjPerturb, weightMat, weightInvMat,
    Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.sub_apply, hHentry,
    Matrix.smul_apply, smul_eq_mul, weightVal, Complex.ofReal_mul, Complex.ofReal_sub,
    Complex.ofReal_one, Complex.ofReal_exp]
  let A : ℂ := (↑APrimeFirstCellJGAllTime.ctAlpha : ℂ) *
    ↑(zdist (B.L N) (x - b) : ℝ)
  let C : ℂ := (↑(-APrimeFirstCellJGAllTime.ctAlpha) : ℂ) *
    ↑(zdist (B.L N) (y - b) : ℝ)
  let E : ℂ := (↑APrimeFirstCellJGAllTime.ctAlpha : ℂ) *
    (↑(zdist (B.L N) (x - b) : ℝ) - ↑(zdist (B.L N) (y - b) : ℝ))
  have hexp : Complex.exp A * Complex.exp C = Complex.exp E := by
    rw [← Complex.exp_add]
    congr 1
    simp only [A, C, E, Complex.ofReal_neg]
    ring
  change Complex.exp A *
      (((Real.sqrt u : ℝ) : ℂ) * APrimeFirstCellJGAllTime.xBlock N ω x y p q) *
      Complex.exp C -
        ((Real.sqrt u : ℝ) : ℂ) * APrimeFirstCellJGAllTime.xBlock N ω x y p q =
    ((Real.sqrt u : ℝ) : ℂ) * (Complex.exp E - 1) *
      APrimeFirstCellJGAllTime.xBlock N ω x y p q
  calc
    Complex.exp A * (((Real.sqrt u : ℝ) : ℂ) *
          APrimeFirstCellJGAllTime.xBlock N ω x y p q) * Complex.exp C -
        ((Real.sqrt u : ℝ) : ℂ) * APrimeFirstCellJGAllTime.xBlock N ω x y p q =
      (((Real.sqrt u : ℝ) : ℂ) * APrimeFirstCellJGAllTime.xBlock N ω x y p q) *
        (Complex.exp A * Complex.exp C - 1) := by ring
    _ = (((Real.sqrt u : ℝ) : ℂ) * APrimeFirstCellJGAllTime.xBlock N ω x y p q) *
        (Complex.exp E - 1) := by rw [hexp]
    _ = ((Real.sqrt u : ℝ) : ℂ) * (Complex.exp E - 1) *
        APrimeFirstCellJGAllTime.xBlock N ω x y p q := by ring

theorem norm_perturbBlock_le_eighth (N : ℕ) (u : ℝ) (ω : Gauss.Ω d)
    (hu : u ∈ Set.Icc (0 : ℝ) (1 / 2)) (hω : ω ∈ APrimeFirstCellJGAllTime.good N)
    (b x y : ZMod (B.L N)) (hxy : x ≠ y)
    (hnear : zdist (B.L N) (x - y) ≤ 1) :
    ‖perturbBlock N u ω b x y‖ ≤ 1 / 8 := by
  rw [perturbBlock_eq_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hsqrt : Real.sqrt u ≤ 1 := by
    rw [Real.sqrt_le_one]
    exact hu.2.trans (by norm_num)
  have hdiff := abs_weight_ratio_sub_one_le N b x y hnear
  have hblock : ‖APrimeFirstCellJGAllTime.xBlock N ω x y‖ ≤ 8 :=
    hω.2 x y hxy hnear
  have hnonneg : 0 ≤
      |Real.exp (APrimeFirstCellJGAllTime.ctAlpha *
        ((zdist (B.L N) (x - b) : ℝ) - (zdist (B.L N) (y - b) : ℝ))) - 1| :=
    abs_nonneg _
  have hb0 : 0 ≤ ‖APrimeFirstCellJGAllTime.xBlock N ω x y‖ := norm_nonneg _
  have hprod : Real.sqrt u *
      |Real.exp (APrimeFirstCellJGAllTime.ctAlpha *
        ((zdist (B.L N) (x - b) : ℝ) - (zdist (B.L N) (y - b) : ℝ))) - 1| ≤
      1 * (1 / 64) :=
    mul_le_mul hsqrt hdiff hnonneg (by norm_num)
  calc
    Real.sqrt u *
        |Real.exp (APrimeFirstCellJGAllTime.ctAlpha *
          ((zdist (B.L N) (x - b) : ℝ) - (zdist (B.L N) (y - b) : ℝ))) - 1| *
          ‖APrimeFirstCellJGAllTime.xBlock N ω x y‖
      ≤ (1 * (1 / 64)) * 8 := mul_le_mul hprod hblock hb0 (by positivity)
    _ = 1 / 8 := by norm_num

theorem perturbBlock_self_eq_zero (N : ℕ) (u : ℝ) (ω : Gauss.Ω d)
    (b x : ZMod (B.L N)) : perturbBlock N u ω b x x = 0 := by
  rw [perturbBlock_eq_smul]
  have hc :
      ((Real.sqrt u *
        (Real.exp (APrimeFirstCellJGAllTime.ctAlpha *
          ((zdist (B.L N) (x - b) : ℝ) - (zdist (B.L N) (x - b) : ℝ))) - 1) : ℝ) : ℂ) = 0 := by
    simp
  rw [hc, zero_smul]

theorem perturbBlock_eq_zero_of_far (N : ℕ) (u : ℝ) (ω : Gauss.Ω d)
    (hω : ω ∈ APrimeFirstCellJGAllTime.good N)
    (b x y : ZMod (B.L N)) (hfar : 1 < zdist (B.L N) (x - y)) :
    perturbBlock N u ω b x y = 0 := by
  rw [perturbBlock_eq_smul]
  have hblock : APrimeFirstCellJGAllTime.xBlock N ω x y = 0 := by
    ext p q
    exact hω.1 x y hfar p q
  rw [hblock, smul_zero]

theorem conjPerturb_mulVec_eq_neighbors
    (N : ℕ) (u : ℝ) (ω : Gauss.Ω d)
    (hω : ω ∈ APrimeFirstCellJGAllTime.good N)
    (b : ZMod (B.L N)) (v : B.Idx N → ℂ)
    (x : ZMod (B.L N)) (p : Fin (B.W N)) :
    (conjPerturb N u ω b *ᵥ v) (x, p) =
      (perturbBlock N u ω b x (x + 1) *ᵥ (fun q => v (x + 1, q))) p +
      (perturbBlock N u ω b x (x - 1) *ᵥ (fun q => v (x - 1, q))) p := by
  classical
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
  let f : ZMod (B.L N) → ℂ := fun y =>
    ∑ q : Fin (B.W N), conjPerturb N u ω b (x, p) (y, q) * v (y, q)
  change (∑ y : ZMod (B.L N), f y) = f (x + 1) + f (x - 1)
  have hpm : x + 1 ≠ x - 1 := by
    intro h
    have htwo : (2 : ZMod (B.L N)) = 0 := by linear_combination h
    exact two_ne_zero_zmod (B.L N) (d.three_le_L N) htwo
  calc
    (∑ y : ZMod (B.L N), f y) =
        ∑ y : ZMod (B.L N),
          if y = x + 1 then f y else if y = x - 1 then f y else 0 := by
      apply Finset.sum_congr rfl
      intro y hy
      by_cases hyp : y = x + 1
      · simp [hyp]
      by_cases hym : y = x - 1
      · simp [hyp, hym]
      simp only [hyp, hym, ↓reduceIte]
      have hblock : perturbBlock N u ω b x y = 0 := by
        by_cases hyx : y = x
        · subst y
          exact perturbBlock_self_eq_zero N u ω b x
        · by_cases hnear : zdist (B.L N) (x - y) ≤ 1
          · rcases eq_zero_or_eq_one_or_eq_neg_one_of_zdist_le_one
                (B.L N) (d.three_le_L N) (x - y) hnear with hzero | hone | hneg
            · exact (hyx (sub_eq_zero.mp hzero).symm).elim
            · have hx : x = y + 1 := (sub_eq_iff_eq_add').mp hone
              have : y = x - 1 := (eq_sub_iff_add_eq).2 hx.symm
              exact (hym this).elim
            · have hx : x = y + (-1) := (sub_eq_iff_eq_add').mp hneg
              have : y = x + 1 := by
                calc
                  y = (y + (-1)) + 1 := by abel
                  _ = x + 1 := by rw [← hx]
              exact (hyp this).elim
          · exact perturbBlock_eq_zero_of_far N u ω hω b x y (by omega)
      have hentry : ∀ q : Fin (B.W N),
          conjPerturb N u ω b (x, p) (y, q) = 0 := by
        intro q
        exact congrFun (congrFun hblock p) q
      simp only [f, hentry, zero_mul, Finset.sum_const_zero]
    _ = f (x + 1) + f (x - 1) := by
      have hite (y : ZMod (B.L N)) :
          (if y = x + 1 then f y else if y = x - 1 then f y else 0) =
            (if y = x + 1 then f y else 0) +
              (if y = x - 1 then f y else 0) := by
        by_cases hyp : y = x + 1
        · subst y
          simp only [if_pos, if_neg hpm, add_zero]
        · rw [if_neg hyp, if_neg hyp, zero_add]
      rw [Finset.sum_congr rfl (fun y _ => hite y), Finset.sum_add_distrib,
        Fintype.sum_ite_eq', Fintype.sum_ite_eq']

set_option maxHeartbeats 800000 in
theorem l2_opNorm_le_two_mul_of_two_neighbor_blocks {G W : Type*} [Fintype G] [DecidableEq G]
    [AddCommGroup G] [Fintype W] [DecidableEq W] [Nonempty (G × W)]
    (s : G) (A : Matrix (G × W) (G × W) ℂ)
    (P M : G → Matrix W W ℂ) (c : ℝ) (hc : 0 ≤ c)
    (hP : ∀ x, ‖P x‖ ≤ c) (hM : ∀ x, ‖M x‖ ≤ c)
    (hact : ∀ (v : (G × W) → ℂ) (x : G) (p : W),
      (A *ᵥ v) (x,p) =
        (P x *ᵥ (fun q => v (x + s, q))) p +
        (M x *ᵥ (fun q => v (x - s, q))) p) :
    ‖A‖ ≤ 2 * c := by
  rw [← Matrix.l2_opNorm_toEuclideanCLM]
  let T : EuclideanSpace ℂ (G × W) →L[ℂ] EuclideanSpace ℂ (G × W) := Matrix.toEuclideanCLM (n := G × W) (𝕜 := ℂ) A
  refine T.opNorm_le_bound (M := 2 * c) (by positivity) fun v => ?_
  have hrhs : 0 ≤ (2 * c) * ‖v‖ := mul_nonneg (mul_nonneg (by norm_num) hc) (norm_nonneg _)
  refine (sq_le_sq₀ (norm_nonneg _) hrhs).mp ?_
  have hvnorm : ‖v‖ ^ 2 = ∑ x : G,
      ‖(WithLp.toLp 2 (fun q : W => v.ofLp (x,q)) : EuclideanSpace ℂ W)‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [EuclideanSpace.norm_sq_eq]
    rw [Fintype.sum_prod_type]
  have hrow (x : G) :
      ‖(WithLp.toLp 2 (fun p : W => (A *ᵥ v.ofLp) (x,p)) : EuclideanSpace ℂ W)‖ ≤
        c * ‖(WithLp.toLp 2 (fun q : W => v.ofLp (x + s,q)) : EuclideanSpace ℂ W)‖ +
        c * ‖(WithLp.toLp 2 (fun q : W => v.ofLp (x - s,q)) : EuclideanSpace ℂ W)‖ := by
    let vp : EuclideanSpace ℂ W := WithLp.toLp 2 (fun q => v.ofLp (x + s,q))
    let vm : EuclideanSpace ℂ W := WithLp.toLp 2 (fun q => v.ofLp (x - s,q))
    have hEq : (WithLp.toLp 2 (fun p : W => (A *ᵥ v.ofLp) (x,p)) : EuclideanSpace ℂ W) =
        Matrix.toEuclideanCLM (n := W) (𝕜 := ℂ) (P x) vp + Matrix.toEuclideanCLM (n := W) (𝕜 := ℂ) (M x) vm := by
      ext p
      simp only [Matrix.toEuclideanCLM_toLp, WithLp.ofLp_toLp, Pi.add_apply, vp, vm]
      exact hact v.ofLp x p
    rw [hEq]
    calc
      ‖Matrix.toEuclideanCLM (n := W) (𝕜 := ℂ) (P x) vp + Matrix.toEuclideanCLM (n := W) (𝕜 := ℂ) (M x) vm‖
          ≤ ‖Matrix.toEuclideanCLM (n := W) (𝕜 := ℂ) (P x) vp‖ + ‖Matrix.toEuclideanCLM (n := W) (𝕜 := ℂ) (M x) vm‖ := norm_add_le _ _
      _ ≤ ‖P x‖ * ‖vp‖ + ‖M x‖ * ‖vm‖ := add_le_add
        ((Matrix.toEuclideanCLM (n := W) (𝕜 := ℂ) (P x)).le_opNorm vp)
        ((Matrix.toEuclideanCLM (n := W) (𝕜 := ℂ) (M x)).le_opNorm vm)
      _ ≤ c * ‖vp‖ + c * ‖vm‖ := add_le_add
        (mul_le_mul_of_nonneg_right (hP x) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _))
  have hTv : T v = WithLp.toLp 2 (A *ᵥ v.ofLp) := by
    simpa only [T] using
      (Matrix.toEuclideanCLM_toLp (n := G × W) (𝕜 := ℂ) A v.ofLp)
  have hout : ‖T v‖ ^ 2 = ∑ x : G,
      ‖(WithLp.toLp 2 (fun p : W => (A *ᵥ v.ofLp) (x,p)) : EuclideanSpace ℂ W)‖ ^ 2 := by
    rw [hTv, EuclideanSpace.norm_sq_eq]
    simp only [EuclideanSpace.norm_sq_eq]
    rw [Fintype.sum_prod_type]
  rw [hout]
  calc
    ∑ x : G, ‖(WithLp.toLp 2 (fun p : W => (A *ᵥ v.ofLp) (x,p)) : EuclideanSpace ℂ W)‖ ^ 2
        ≤ ∑ x : G, (c * ‖(WithLp.toLp 2 (fun q : W => v.ofLp (x + s,q)) : EuclideanSpace ℂ W)‖ +
          c * ‖(WithLp.toLp 2 (fun q : W => v.ofLp (x - s,q)) : EuclideanSpace ℂ W)‖) ^ 2 :=
      Finset.sum_le_sum fun x _ => pow_le_pow_left₀ (norm_nonneg _) (hrow x) 2
    _ ≤ ∑ x : G, 2 * (c^2 * ‖(WithLp.toLp 2 (fun q : W => v.ofLp (x + s,q)) : EuclideanSpace ℂ W)‖^2 +
          c^2 * ‖(WithLp.toLp 2 (fun q : W => v.ofLp (x - s,q)) : EuclideanSpace ℂ W)‖^2) := by
      apply Finset.sum_le_sum
      intro x hx
      nlinarith [sq_nonneg (c * ‖(WithLp.toLp 2 (fun q : W => v.ofLp (x + s,q)) : EuclideanSpace ℂ W)‖ -
        c * ‖(WithLp.toLp 2 (fun q : W => v.ofLp (x - s,q)) : EuclideanSpace ℂ W)‖)]
    _ = 4 * c^2 * ‖v‖^2 := by
      let f : G → ℝ := fun x => ‖(WithLp.toLp 2
        (fun q : W => v.ofLp (x,q)) : EuclideanSpace ℂ W)‖ ^ 2
      have hp : (∑ x : G, ‖(WithLp.toLp 2 (fun q : W => v.ofLp (x + s,q)) : EuclideanSpace ℂ W)‖ ^ 2) = ‖v‖^2 := by
        calc
          _ = ∑ x : G, f ((Equiv.addRight s) x) := by rfl
          _ = ∑ x : G, f x := Equiv.sum_comp (Equiv.addRight s) f
          _ = ‖v‖^2 := by simpa only [f] using hvnorm.symm
      have hm : (∑ x : G, ‖(WithLp.toLp 2 (fun q : W => v.ofLp (x - s,q)) : EuclideanSpace ℂ W)‖ ^ 2) = ‖v‖^2 := by
        calc
          _ = ∑ x : G, f ((Equiv.subRight s) x) := by simp only [Equiv.subRight_apply, f]
          _ = ∑ x : G, f x := Equiv.sum_comp (Equiv.subRight s) f
          _ = ‖v‖^2 := by simpa only [f] using hvnorm.symm
      rw [← Finset.mul_sum, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, hp, hm]
      ring
    _ = ((2*c) * ‖v‖)^2 := by ring

theorem norm_conjPerturb_le_quarter
    (N : ℕ) (u : ℝ) (ω : Gauss.Ω d)
    (hu : u ∈ Set.Icc (0 : ℝ) (1 / 2))
    (hω : ω ∈ APrimeFirstCellJGAllTime.good N)
    (b : ZMod (B.L N)) : ‖conjPerturb N u ω b‖ ≤ 1 / 4 := by
  have hplus (x : ZMod (B.L N)) :
      ‖perturbBlock N u ω b x (x + 1)‖ ≤ 1 / 8 := by
    apply norm_perturbBlock_le_eighth N u ω hu hω
    · intro h
      have h01 : (0 : ZMod (B.L N)) = 1 := by
        have hx : x + (0 : ZMod (B.L N)) = x + 1 := (add_zero x).trans h
        exact add_left_cancel hx
      apply one_ne_zero_zmod (B.L N) (d.three_le_L N)
      exact h01.symm
    · have heq : x - (x + 1) = (-1 : ZMod (B.L N)) := by abel
      rw [heq]
      exact zdist_neg_one_le (B.L N) (d.three_le_L N)
  have hminus (x : ZMod (B.L N)) :
      ‖perturbBlock N u ω b x (x - 1)‖ ≤ 1 / 8 := by
    apply norm_perturbBlock_le_eighth N u ω hu hω
    · intro h
      have h01 : (0 : ZMod (B.L N)) = 1 := by
        calc
          0 = x - x := (sub_self x).symm
          _ = x - (x - 1) := congrArg (fun y => x - y) h
          _ = 1 := by abel
      apply one_ne_zero_zmod (B.L N) (d.three_le_L N)
      exact h01.symm
    · have heq : x - (x - 1) = (1 : ZMod (B.L N)) := by abel
      rw [heq]
      exact zdist_one_le (B.L N) (d.three_le_L N)
  have h := l2_opNorm_le_two_mul_of_two_neighbor_blocks
    (G := ZMod (B.L N)) (W := Fin (B.W N)) (1 : ZMod (B.L N))
    (conjPerturb N u ω b)
    (fun x => perturbBlock N u ω b x (x + 1))
    (fun x => perturbBlock N u ω b x (x - 1))
    (1 / 8) (by norm_num) hplus hminus
    (conjPerturb_mulVec_eq_neighbors N u ω hω b)
  norm_num at h ⊢
  exact h

theorem conjugated_sub_smul (N : ℕ) (u : ℝ) (ω : Gauss.Ω d)
    (b : ZMod (B.L N)) (z : ℂ) :
    weightMat N b *
        ((Gauss.sample d).H N u ω - z • (1 : Matrix (B.Idx N) (B.Idx N) ℂ)) *
        weightInvMat N b =
      ((Gauss.sample d).H N u ω - z • (1 : Matrix (B.Idx N) (B.Idx N) ℂ)) +
        conjPerturb N u ω b := by
  rw [conjPerturb]
  have hDI := weight_mul_inv N b
  rw [Matrix.mul_sub, Matrix.sub_mul]
  have hz : weightMat N b * (z • (1 : Matrix (B.Idx N) (B.Idx N) ℂ)) *
      weightInvMat N b = z • (1 : Matrix (B.Idx N) (B.Idx N) ℂ) := by
    simp only [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul,
      ← Matrix.mul_assoc, hDI, smul_eq_mul, mul_one]
  rw [hz]
  noncomm_ring

-- Resolvent norm after an abstract weighted similarity.  This is the
-- Neumann estimate written as `Q + G K Q = G`; it retains the constants
-- `2`, `1/4`, and `4` exactly.  Matrix norm elaboration is expensive here.
set_option maxHeartbeats 800000 in
theorem norm_conjugated_green_le_four {n : Type*} [Fintype n] [DecidableEq n]
    [Nonempty n]
    (H D Di K : Matrix n n ℂ) (z : ℂ) (hH : H.IsHermitian)
    (hz : z.im ≠ 0) (hzim : |z.im|⁻¹ ≤ 2)
    (hDDi : D * Di = 1) (hDiD : Di * D = 1)
    (hconj : D * (H - z • (1 : Matrix n n ℂ)) * Di =
      (H - z • (1 : Matrix n n ℂ)) + K)
    (hK : ‖K‖ ≤ 1 / 4) :
    ‖D * green H z * Di‖ ≤ 4 := by
  let A := H - z • (1 : Matrix n n ℂ)
  let G := green H z
  let Q := D * G * Di
  have hG : ‖G‖ ≤ 2 := (norm_green_le hH hz).trans hzim
  have hAG : A * G = 1 := sub_mul_green_of_im hH hz
  have hGA : G * A = 1 := green_mul_sub_of_im hH hz
  have hconj' : D * A * Di = A + K := hconj
  have hAQ : (A + K) * Q = 1 := by
    rw [← hconj']
    dsimp only [Q]
    calc
      (D * A * Di) * (D * G * Di) = D * A * (Di * D) * G * Di := by
        noncomm_ring
      _ = D * (A * G) * Di := by rw [hDiD]; noncomm_ring
      _ = D * Di := by rw [hAG, mul_one]
      _ = 1 := hDDi
  have hres : Q + G * K * Q = G := by
    calc
      Q + G * K * Q = G * A * Q + G * K * Q := by rw [hGA, one_mul]
      _ = G * ((A + K) * Q) := by noncomm_ring
      _ = G := by rw [hAQ, mul_one]
  have hqeq : Q = G - G * K * Q := by
    exact (eq_sub_iff_add_eq).2 hres
  have hqeq' : Q = G - G * (K * Q) := by
    simpa only [Matrix.mul_assoc] using hqeq
  have htri : ‖Q‖ ≤ ‖G‖ + ‖G * (K * Q)‖ := by
    calc
      ‖Q‖ = ‖G - G * (K * Q)‖ := congrArg norm hqeq'
      _ ≤ ‖G‖ + ‖G * (K * Q)‖ := norm_sub_le G (G * (K * Q))
  have hmulG : ‖G * (K * Q)‖ ≤ ‖G‖ * ‖K * Q‖ := norm_mul_le _ _
  have hmulK : ‖K * Q‖ ≤ ‖K‖ * ‖Q‖ := norm_mul_le _ _
  have hK' : ‖K‖ ≤ 1 / 4 := hK
  have hQ0 : 0 ≤ ‖Q‖ := norm_nonneg _
  have hG0 : 0 ≤ ‖G‖ := norm_nonneg _
  have hK0 : 0 ≤ ‖K‖ := norm_nonneg _
  have hGKQ0 : 0 ≤ ‖G * (K * Q)‖ := norm_nonneg _
  have hKQ0 : 0 ≤ ‖K * Q‖ := norm_nonneg _
  change ‖Q‖ ≤ 4
  nlinarith [mul_le_mul_of_nonneg_left hmulK hG0]

/-- The preceding abstract estimate for the cyclic exponential weight. -/
theorem norm_weighted_green_le_four
    (N : ℕ) (u : ℝ) (ω : Gauss.Ω d) (b : ZMod (B.L N)) (z : ℂ)
    (hz : z.im ≠ 0) (hzim : |z.im|⁻¹ ≤ 2)
    (hK : ‖conjPerturb N u ω b‖ ≤ 1 / 4) :
    ‖weightMat N b * green ((Gauss.sample d).H N u ω) z * weightInvMat N b‖ ≤ 4 := by
  exact norm_conjugated_green_le_four
    ((Gauss.sample d).H N u ω) (weightMat N b) (weightInvMat N b)
    (conjPerturb N u ω b) z ((Gauss.sample d).hermitian N u ω)
    hz hzim (weight_mul_inv N b) (inv_mul_weight N b)
    (conjugated_sub_smul N u ω b z) hK

theorem green_entry_decay_of_conjPerturb_norm
    (N : ℕ) (u : ℝ) (ω : Gauss.Ω d) (z : ℂ)
    (hz : z.im ≠ 0) (hzim : |z.im|⁻¹ ≤ 2)
    (hK : ∀ b : ZMod (B.L N), ‖conjPerturb N u ω b‖ ≤ 1 / 4)
    (a b : ZMod (B.L N)) (p q : Fin (B.W N)) :
    ‖green ((Gauss.sample d).H N u ω) z (a, p) (b, q)‖ ≤
      4 * Real.exp (-APrimeFirstCellJGAllTime.ctAlpha *
        (zdist (B.L N) (a - b) : ℝ)) := by
  have hQ := norm_weighted_green_le_four N u ω b z hz hzim (hK b)
  have hentry := norm_apply_le_l2_opNorm
    (weightMat N b * green ((Gauss.sample d).H N u ω) z * weightInvMat N b)
    (a, p) (b, q)
  have hentry4 := hentry.trans hQ
  have hformula :
      (weightMat N b * green ((Gauss.sample d).H N u ω) z * weightInvMat N b)
          (a, p) (b, q) =
        (Real.exp (APrimeFirstCellJGAllTime.ctAlpha *
          (zdist (B.L N) (a - b) : ℝ)) : ℂ) *
          green ((Gauss.sample d).H N u ω) z (a, p) (b, q) := by
    simp only [weightMat, weightInvMat, Matrix.diagonal_mul, Matrix.mul_diagonal,
      Matrix.diagonal_apply_eq, sub_self, zdist_zero, Nat.cast_zero, mul_zero,
      neg_zero, Real.exp_zero, Complex.ofReal_one, mul_one]
    rw [weightVal]
  rw [hformula, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le] at hentry4
  let x : ℝ := APrimeFirstCellJGAllTime.ctAlpha *
    (zdist (B.L N) (a - b) : ℝ)
  calc
    ‖green ((Gauss.sample d).H N u ω) z (a, p) (b, q)‖
        = Real.exp (-x) *
            (Real.exp x * ‖green ((Gauss.sample d).H N u ω) z (a, p) (b, q)‖) := by
          rw [← mul_assoc, ← Real.exp_add]
          simp
    _ ≤ Real.exp (-x) * 4 := mul_le_mul_of_nonneg_left hentry4 (Real.exp_pos _).le
    _ = 4 * Real.exp (-APrimeFirstCellJGAllTime.ctAlpha *
        (zdist (B.L N) (a - b) : ℝ)) := by simp [x, mul_comm]

theorem Gsig_entry_decay_on_good
    (N : ℕ) (u : ℝ) (ω : Gauss.Ω d)
    (hu : u ∈ Set.Icc (0 : ℝ) (1 / 2))
    (hω : ω ∈ APrimeFirstCellJGAllTime.good N)
    (sigma : Bool) (a b : ZMod (B.L N))
    (p q : Fin (B.W N)) :
    ‖Gsig ((Gauss.sample d).H N u ω) (zt 0 u) sigma (a, p) (b, q)‖ ≤
      4 * Real.exp (-APrimeFirstCellJGAllTime.ctAlpha *
        (zdist (B.L N) (a - b) : ℝ)) := by
  let zsigma : ℂ := if sigma then zt 0 u else (starRingEnd ℂ) (zt 0 u)
  have hm : mE 0 = Complex.I := by
    rw [mE]
    norm_num
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    push_cast
    ring
  have him : (zt 0 u).im = 1 - u := by
    rw [zt_im]
    rw [hm]
    norm_num
  have hpos : 0 < 1 - u := by linarith [hu.2]
  have habs : |zsigma.im| = 1 - u := by
    cases sigma
    · simp only [zsigma, Bool.false_eq_true, ↓reduceIte, Complex.conj_im, him]
      rw [abs_of_nonpos]
      · ring
      · linarith [hu.2]
    · simp [zsigma, him, abs_of_pos hpos]
  have hz : zsigma.im ≠ 0 := by
    intro hz
    rw [hz, abs_zero] at habs
    linarith
  have hzim : |zsigma.im|⁻¹ ≤ 2 := by
    rw [habs]
    apply (inv_le_comm₀ hpos (by norm_num : (0 : ℝ) < 2)).2
    norm_num
    linarith [hu.2]
  have hdecay := green_entry_decay_of_conjPerturb_norm
    N u ω zsigma hz hzim (fun c => norm_conjPerturb_le_quarter N u ω hu hω c)
    a b p q
  simpa only [Gsig, zsigma] using hdecay

theorem green_entry_decay_on_good
    (N : ℕ) (u : ℝ) (ω : Gauss.Ω d)
    (hu : u ∈ Set.Icc (0 : ℝ) (1 / 2))
    (hω : ω ∈ APrimeFirstCellJGAllTime.good N)
    (a b : ZMod (B.L N)) (p q : Fin (B.W N)) :
    ‖green ((Gauss.sample d).H N u ω) (zt 0 u) (a, p) (b, q)‖ ≤
      4 * Real.exp (-APrimeFirstCellJGAllTime.ctAlpha *
        (zdist (B.L N) (a - b) : ℝ)) := by
  simpa only [Gsig_true] using
    Gsig_entry_decay_on_good N u ω hu hω true a b p q

theorem eventually_all_time_jG_le_two_on_good :
    ∀ᶠ N : ℕ in atTop, ∀ ω ∈ APrimeFirstCellJGAllTime.good N,
      ∀ u ∈ Set.Icc (0 : ℝ) (1 / 2),
        APrimeJG.jG (Gauss.sample d) 0 N u ω
          ((Gauss.band d).ell N u) (etaT 0 u) 60 ≤ 2 := by
  filter_upwards [APrimeFirstCellJGAllTime.eventually_floor_bound] with N hfloor
  intro ω hω
  exact APrimeFirstCellJGAllTime.all_time_jG_le_two_of_green_decay N ω
    (fun u hu => green_entry_decay_on_good N u ω hu hω) hfloor

noncomputable def diagonalWitness : Gauss.Ω d := fun c =>
  if c.2.1 = c.2.2.1 ∧ c.2.2.2 = true then 1 else 0

theorem Xentry_diagonalWitness (N : ℕ) (i j : d.Idx N) :
    Xentry d N diagonalWitness i j = if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    simp [Xentry, diagonalWitness]
  · simp only [Xentry]
    split_ifs with hlt hgt
    · simp [diagonalWitness, hij]
    · simp [diagonalWitness, Ne.symm hij]
    · simp [diagonalWitness, hij]

theorem diagonalWitness_mem_good (N : ℕ) :
    diagonalWitness ∈ APrimeFirstCellJGAllTime.good N := by
  constructor
  · intro x y hfar p q
    have hxy : x ≠ y := by
      intro h
      subst y
      simp only [sub_self, zdist_zero] at hfar
      omega
    rw [APrimeFirstCellJGAllTime.xBlock, Xmat_apply,
      Xentry_diagonalWitness, if_neg (by
        intro h
        exact hxy (congrArg (fun z : B.Idx N => z.1) h))]
  · intro x y hxy hnear
    have hzero : APrimeFirstCellJGAllTime.xBlock N diagonalWitness x y = 0 := by
      ext p q
      change Xentry d N diagonalWitness (x, p) (y, q) = 0
      rw [
        Xentry_diagonalWitness, if_neg (by
          intro h
          exact hxy (congrArg (fun z : B.Idx N => z.1) h))]
    rw [hzero, norm_zero]
    norm_num

theorem Xmat_diagonalWitness_ne_zero (N : ℕ) :
    Xmat d N diagonalWitness ≠ 0 := by
  let p : Fin (d.W N) := ⟨0, d.W_pos N⟩
  let i : d.Idx N := (0, p)
  intro hzero
  have hone : Xmat d N diagonalWitness i i = 1 := by
    rw [Xmat_apply, Xentry_diagonalWitness, if_pos rfl]
  have hz : Xmat d N diagonalWitness i i = 0 := by rw [hzero]; rfl
  rw [hz] at hone
  exact zero_ne_one hone

#print axioms abs_weight_ratio_sub_one_le
#print axioms norm_perturbBlock_le_eighth
#print axioms l2_opNorm_le_two_mul_of_two_neighbor_blocks
#print axioms norm_conjPerturb_le_quarter
#print axioms norm_conjugated_green_le_four
#print axioms Gsig_entry_decay_on_good
#print axioms eventually_all_time_jG_le_two_on_good
#print axioms diagonalWitness_mem_good
#print axioms Xmat_diagonalWitness_ne_zero

end RBM.APrimeFirstCellCTDecay
