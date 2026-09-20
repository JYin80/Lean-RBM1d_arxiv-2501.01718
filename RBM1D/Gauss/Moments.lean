/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Stein

/-!
# Moments of a centred real Gaussian

The even moments, from the one-dimensional Stein identity of `Gauss/Stein.lean`:
taking `f x = x^{2p+1}` in `E[X f(X)] = v E[f'(X)]` gives the recursion

  `E[X^{2p+2}] = (2p+1) · v · E[X^{2p}]`,

hence `E[X^{2p}] = (2p-1)!! · v^p`.  This is the deterministic input of the large deviation
estimates of T81/T82: conditionally on the other coordinates, the linear form
`∑_k H_{ik} X_k` is a centred Gaussian, and its moments are read off from this formula.

## Main statements

* `RBM.integrable_pow_gaussianReal` : all polynomial moments exist
* `RBM.integral_pow_gaussianReal_succ` : the Stein recursion
* `RBM.integral_pow_gaussianReal` : `E[X^{2p}] = (∏_{i<p} (2i+1)) v^p`, valid also at `v = 0`
-/

namespace RBM

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal ENNReal

section Moments

/-- Every polynomial is integrable against a real Gaussian. -/
theorem integrable_pow_gaussianReal (v : ℝ≥0) (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k) (gaussianReal 0 v) := by
  have hmem : MemLp (id : ℝ → ℝ) (k : ℝ≥0∞) (gaussianReal 0 v) :=
    memLp_id_gaussianReal' _ (by simp)
  have h := hmem.integrable_norm_pow' (p := k)
  refine h.mono (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
  simp

/-- Transfer integrability from the Gaussian measure to the density form used by
`RBM.integral_mul_gaussianReal`. -/
theorem integrable_mul_gaussianPDFReal {v : ℝ≥0} (hv : v ≠ 0) {g : ℝ → ℝ}
    (hg : Integrable g (gaussianReal 0 v)) :
    Integrable fun x : ℝ => g x * gaussianPDFReal 0 v x := by
  rw [gaussianReal_of_var_ne_zero _ hv,
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF _ _)
      (Filter.Eventually.of_forall fun _ => gaussianPDF_lt_top)] at hg
  simpa [gaussianPDF_def, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg 0 v _),
    mul_comm] using hg

/-- **The Stein recursion for the even moments**: `E[X^{2p+2}] = (2p+1) v E[X^{2p}]`. -/
theorem integral_pow_gaussianReal_succ (v : ℝ≥0) (p : ℕ) :
    ∫ x : ℝ, x ^ (2 * p + 2) ∂(gaussianReal 0 v)
      = (2 * p + 1) * (v : ℝ) * ∫ x : ℝ, x ^ (2 * p) ∂(gaussianReal 0 v) := by
  by_cases hv : v = 0
  · subst hv
    rw [gaussianReal_zero_var, integral_dirac, integral_dirac]
    simp
  have hf : ∀ x : ℝ, HasDerivAt (fun y : ℝ => y ^ (2 * p + 1))
      ((2 * p + 1 : ℕ) * x ^ (2 * p)) x := by
    intro x
    simpa using hasDerivAt_pow (2 * p + 1) x
  have h1 : Integrable fun x : ℝ =>
      x ^ (2 * p + 1) * (-(x / (v : ℝ)) * gaussianPDFReal 0 v x) := by
    have := integrable_mul_gaussianPDFReal hv
      (g := fun x : ℝ => -((v : ℝ)⁻¹) * x ^ (2 * p + 2))
      (((integrable_pow_gaussianReal v (2 * p + 2)).const_mul _))
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    field_simp
    ring
  have h2 : Integrable fun x : ℝ =>
      ((2 * p + 1 : ℕ) : ℝ) * x ^ (2 * p) * gaussianPDFReal 0 v x :=
    integrable_mul_gaussianPDFReal hv
      ((integrable_pow_gaussianReal v (2 * p)).const_mul _)
  have h3 : Integrable fun x : ℝ => x ^ (2 * p + 1) * gaussianPDFReal 0 v x :=
    integrable_mul_gaussianPDFReal hv (integrable_pow_gaussianReal v (2 * p + 1))
  have h := integral_mul_gaussianReal hv hf h1 h2 h3
  rw [show (fun x : ℝ => x * x ^ (2 * p + 1)) = fun x : ℝ => x ^ (2 * p + 2) from by
    funext x; ring] at h
  rw [h, integral_const_mul]
  push_cast
  ring

/-- **The even moments of a centred real Gaussian**: `E[X^{2p}] = (2p-1)!!·v^p`, with the
double factorial written as `∏_{i<p} (2i+1)`. -/
theorem integral_pow_gaussianReal (v : ℝ≥0) (p : ℕ) :
    ∫ x : ℝ, x ^ (2 * p) ∂(gaussianReal 0 v)
      = (∏ i ∈ range p, (2 * (i : ℝ) + 1)) * (v : ℝ) ^ p := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [show 2 * (p + 1) = 2 * p + 2 from by ring, integral_pow_gaussianReal_succ, ih,
      prod_range_succ]
    ring

/-! ### The modulus of a centred complex Gaussian -/

/-- The double factorial `(2p-1)!! = ∏_{i<p} (2i+1)`, the `2p`-th moment of a standard
Gaussian. -/
noncomputable def dfac (p : ℕ) : ℝ := ∏ i ∈ range p, (2 * (i : ℝ) + 1)

@[simp] theorem dfac_zero : dfac 0 = 1 := by simp [dfac]

theorem dfac_succ (p : ℕ) : dfac (p + 1) = (2 * (p : ℝ) + 1) * dfac p := by
  rw [dfac, dfac, prod_range_succ, mul_comm]

theorem integral_pow_gaussianReal' (v : ℝ≥0) (p : ℕ) :
    ∫ x : ℝ, x ^ (2 * p) ∂(gaussianReal 0 v) = dfac p * (v : ℝ) ^ p :=
  integral_pow_gaussianReal v p

/-- **The convolution identity behind the complex moment**:
`∑_k C(p,k) (2k-1)!! (2(p-k)-1)!! = 2^p p!`.  Pascal's rule turns the sum at `p+1` into
`(2p+2)` times the sum at `p`, because `(2(p-k)+1) + (2k+1) = 2p+2`. -/
theorem sum_choose_dfac (p : ℕ) :
    ∑ k ∈ range (p + 1), (p.choose k : ℝ) * (dfac k * dfac (p - k)) = 2 ^ p * (Nat.factorial p : ℝ) := by
  induction p with
  | zero => simp
  | succ p ih =>
    have hzero : ((p.choose (p + 1) : ℕ) : ℝ) = 0 := by
      rw [Nat.choose_eq_zero_of_lt (Nat.lt_succ_self p)]; norm_num
    -- peel the term `k = 0` and shift the rest
    rw [sum_range_succ' (fun k => ((p + 1).choose k : ℝ) * (dfac k * dfac (p + 1 - k))) (p + 1)]
    have hterm : ∀ j ∈ range (p + 1),
        ((p + 1).choose (j + 1) : ℝ) * (dfac (j + 1) * dfac (p + 1 - (j + 1)))
          = (p.choose j : ℝ) * ((2 * (j : ℝ) + 1) * (dfac j * dfac (p - j)))
            + (p.choose (j + 1) : ℝ) * (dfac (j + 1) * dfac (p - j)) := by
      intro j _
      rw [Nat.choose_succ_succ, Nat.succ_sub_succ, dfac_succ]
      push_cast
      ring
    rw [sum_congr rfl hterm, sum_add_distrib]
    -- the shifted sum is the sum at `p` with `p + 1 - k` in place of `p - k`, minus its `k = 0` term
    have hshift : ∑ j ∈ range (p + 1), (p.choose (j + 1) : ℝ) * (dfac (j + 1) * dfac (p - j))
        = (∑ k ∈ range (p + 1), (p.choose k : ℝ) * (dfac k * dfac (p + 1 - k)))
          - dfac (p + 1) := by
      rw [sum_range_succ' (fun k => (p.choose k : ℝ) * (dfac k * dfac (p + 1 - k))) p,
        sum_range_succ _ p, hzero]
      simp only [Nat.choose_zero_right, Nat.cast_one, dfac_zero, Nat.sub_zero, one_mul, zero_mul,
        add_zero, Nat.succ_sub_succ]
      ring
    have hpk : ∀ k ∈ range (p + 1), (p.choose k : ℝ) * (dfac k * dfac (p + 1 - k))
        = (p.choose k : ℝ) * ((2 * ((p : ℝ) - k) + 1) * (dfac k * dfac (p - k))) := by
      intro k hk
      rw [mem_range, Nat.lt_succ_iff] at hk
      rw [show p + 1 - k = (p - k) + 1 from by omega, dfac_succ]
      have : ((p - k : ℕ) : ℝ) = (p : ℝ) - k := by
        have := Nat.cast_sub (R := ℝ) hk; linarith [this]
      rw [this]
      ring
    rw [hshift, sum_congr rfl hpk]
    -- combine the two sums into `(2p+2)` times the sum at `p`
    have hcomb : ∑ k ∈ range (p + 1),
          (p.choose k : ℝ) * ((2 * ((p : ℝ) - k) + 1) * (dfac k * dfac (p - k)))
        + ∑ j ∈ range (p + 1), (p.choose j : ℝ) * ((2 * (j : ℝ) + 1) * (dfac j * dfac (p - j)))
        = (2 * (p : ℝ) + 2) * ∑ k ∈ range (p + 1), (p.choose k : ℝ) * (dfac k * dfac (p - k)) := by
      rw [← sum_add_distrib, mul_sum]
      refine sum_congr rfl fun k _ => ?_
      ring
    have hdfac : dfac (p + 1) = ((p + 1).choose 0 : ℝ) * (dfac 0 * dfac (p + 1 - 0)) := by
      simp
    rw [← hdfac, ih] at *
    push_cast [Nat.factorial_succ, pow_succ]
    linear_combination hcomb

/-- **The absolute moments of a centred complex Gaussian.**  If `X` and `Y` are independent
centred real Gaussians of variance `w`, then `Z = X + iY` satisfies
`E‖Z‖^{2p} = E[(X² + Y²)^p] = p! (2w)^p = p! σ^{2p}` with `σ² = E‖Z‖² = 2w`. -/
theorem integral_add_sq_pow_gaussian_prod (w : ℝ≥0) (p : ℕ) :
    ∫ z : ℝ × ℝ, (z.1 ^ 2 + z.2 ^ 2) ^ p
        ∂((gaussianReal 0 w).prod (gaussianReal 0 w))
      = (Nat.factorial p : ℝ) * (2 * (w : ℝ)) ^ p := by
  have hexp : ∀ z : ℝ × ℝ, (z.1 ^ 2 + z.2 ^ 2) ^ p
      = ∑ k ∈ range (p + 1), z.1 ^ (2 * k) * z.2 ^ (2 * (p - k)) * (p.choose k : ℝ) := by
    intro z
    rw [add_pow]
    refine sum_congr rfl fun k hk => ?_
    rw [mem_range, Nat.lt_succ_iff] at hk
    rw [← pow_mul, ← pow_mul, mul_comm 2 k, mul_comm 2 (p - k)]
  simp_rw [hexp]
  rw [integral_finsetSum _ (fun k _ => ?_)]
  · have hval : ∀ k ∈ range (p + 1),
        ∫ z : ℝ × ℝ, z.1 ^ (2 * k) * z.2 ^ (2 * (p - k)) * (p.choose k : ℝ)
            ∂((gaussianReal 0 w).prod (gaussianReal 0 w))
          = (p.choose k : ℝ) * (dfac k * dfac (p - k)) * (w : ℝ) ^ p := by
      intro k hk
      rw [mem_range, Nat.lt_succ_iff] at hk
      simp_rw [mul_comm _ ((p.choose k : ℝ))]
      rw [integral_const_mul, integral_prod_mul (fun x : ℝ => x ^ (2 * k))
        (fun y : ℝ => y ^ (2 * (p - k))), integral_pow_gaussianReal', integral_pow_gaussianReal']
      have hw : (w : ℝ) ^ k * (w : ℝ) ^ (p - k) = (w : ℝ) ^ p := by
        rw [← pow_add]
        congr 1
        omega
      rw [← hw]
      ring
    rw [sum_congr rfl hval, ← sum_mul, sum_choose_dfac]
    rw [mul_pow]
    ring
  · exact ((integrable_pow_gaussianReal w (2 * k)).mul_prod
      (integrable_pow_gaussianReal w (2 * (p - k)))).mul_const _

end Moments

end RBM
