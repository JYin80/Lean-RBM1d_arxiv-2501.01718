/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Flow.DBMInput
import RBM1D.Flow.FreeConvStability
import RBM1D.Flow.EventuallyUniformBySequences
import RBM1D.Gauss.TraceMoment

/-!
# The regularity event of Step 1 of Theorem 2.6

The parameters `step1Eps`, `step1Sig`, `step1Prec`, `step1Rate`, `step1CountEps`, `cBulk`,
the shifted-and-rescaled diagonal `vOU`, and the good event `eventually_step1Good`: [51,
Definition 2.1]'s regularity (`IsRegular51`) for `vOU` together with the existence and
closeness (to `rhoSc E₀`) of the free-convolution limit density, uniformly over a mesoscopic
grid, fail with probability `O(N^{-D})`.

## Route

The randomness enters only through `BandTracialLocalLaw d (κ/2)` (`hLL`), the averaged local
semicircle law for the Gaussian band matrix.  `RBM.eventually_forall_of_forall_sequences`
upgrades its "for every admissible deterministic sequence, eventually" form into a single
eventual index `N₀` valid **simultaneously for every** spectral parameter `z` in the domain;
`RBM.HighProb.biInter` then turns the resulting *pointwise* bound on a polynomial-size
`M^{-3}`-grid into a *simultaneous* (union-bound) high-probability statement; the deterministic
Lipschitz bound on the finite-sum Stieltjes transform interpolates from the grid to the
continuum region.  The free-convolution closeness needed by
`FreeConvStability.freeConv_stable_local` is read off the same grid-good event.
-/

open MeasureTheory Filter Matrix Topology Complex

namespace RBM.Gauss

/-! ### Parameters -/

/-- `ε_g = τ_*/4`, the exponent of `g = M^{-1+τ_*/4}`. -/
noncomputable def step1Eps (τs : ℝ) : ℝ := τs / 4

/-- `σ = δ = min(τ_*/4, (1-τ_*)/3)`. -/
noncomputable def step1Sig (τs : ℝ) : ℝ := min (τs / 4) ((1 - τs) / 3)

/-- `τ' = τ_*/8`, the local-law precision. -/
noncomputable def step1Prec (τs : ℝ) : ℝ := τs / 8

/-- The rate `3τ_*/8` of `ρ_fc` closeness to `ρ_sc(E₀)`. -/
noncomputable def step1Rate (τs : ℝ) : ℝ := 3 * τs / 8

/-- The counting-scale exponent `τ_*/(8(k+1))`. -/
noncomputable def step1CountEps (τs : ℝ) (k : ℕ) : ℝ := τs / (8 * (k + 1))

/-- **The shifted, rescaled diagonal**: `v_i = e^{-t_*/2} λ_i(X) - E₀`. -/
noncomputable def vOU (d : Dims) (N : ℕ) (τs E₀ : ℝ) (ω : Ω d) : d.Idx N → ℝ :=
  fun i => ouBandCoeff ((Gauss.band d).tPow τs N) * (Xmat_isHermitian d N ω).eigenvalues i - E₀

/-! ### The eigenvalue ↔ Stieltjes-transform dictionary -/

/-- **`stieltjes` is the finite-sum `stieltjesVec` of the eigenvalues.** -/
private theorem step1_stieltjes_eq_stieltjesVec {n : Type*} [Fintype n] [DecidableEq n]
    {H : Matrix n n ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : 0 < z.im) :
    RBM.stieltjes H z = stieltjesVec hH.eigenvalues z := by
  have hzne : ∀ l, (hH.eigenvalues l : ℂ) ≠ z := fun l h => by
    have h2 : (0 : ℝ) = z.im := by
      have := congrArg Complex.im h
      simpa using this
    linarith
  unfold RBM.stieltjes stieltjesVec
  congr 1
  rw [RBM.green_eq_spectral hH hzne]
  set U : Matrix n n ℂ := (hH.eigenvectorUnitary : Matrix n n ℂ) with hU
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self _
  rw [Matrix.trace_mul_comm (U * diagonal (fun l => ((hH.eigenvalues l : ℂ) - z)⁻¹)) (star U),
    ← Matrix.mul_assoc, hUU, Matrix.one_mul, Matrix.trace_diagonal]

open scoped Matrix.Norms.L2Operator in
/-- **An eigenvalue of a Hermitian matrix is bounded by its `ℓ² → ℓ²` operator norm.** -/
private theorem step1_eigenvalue_abs_le_norm {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (i : n) : |hA.eigenvalues i| ≤ ‖A‖ := by
  set ψ : EuclideanSpace ℂ n := hA.eigenvectorBasis i with hψ_def
  have hψnorm : ‖ψ‖ = 1 := hA.eigenvectorBasis.norm_eq_one i
  have hmv := hA.mulVec_eigenvectorBasis i
  have hCLM : (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A) ψ = ((hA.eigenvalues i : ℝ) : ℂ) • ψ := by
    apply WithLp.ofLp_injective 2
    rw [Matrix.ofLp_toEuclideanCLM, hmv, RCLike.real_smul_eq_coe_smul (K := ℂ),
      WithLp.ofLp_smul, hψ_def]
    rfl

  have hop : ‖(Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A) ψ‖ ≤ ‖A‖ := by
    have h1 := (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A).le_opNorm ψ
    rw [hψnorm, mul_one] at h1
    rwa [← Matrix.cstar_norm_def] at h1
  rw [hCLM, norm_smul, Complex.norm_real, hψnorm, mul_one] at hop
  exact hop

/-! ### The bulk lower bound and Lipschitz continuity of `m_sc`

These duplicate the (private) route of `RBM1D/Flow/FreeConvStability.lean` (§1, `fcs_*`) from
the same public building blocks (`msc_mul`, `msc_im_pos`, `lemT_ge`, `msc_add_eq_neg_inv`),
since that file's helpers are not exported. -/

private lemma step1_quad_diff {a z : ℂ} (ha : a * (a + z) = -1) (z' : ℂ) :
    (msc z' - a) * (a + msc z' + z') = -((z' - z) * a) := by
  have h := msc_mul z'
  linear_combination h - ha

private lemma step1_im_le_denom (a : ℂ) {z' : ℂ} (hz' : 0 < z'.im) :
    a.im ≤ (a + msc z' + z').im := by
  have h := msc_add_eq_neg_inv hz'
  have hm := msc_im_pos hz'
  have hne : msc z' ≠ 0 := fun h0 => by rw [h0, Complex.zero_im] at hm; exact lt_irrefl _ hm
  have hpos : 0 < (msc z' + z').im := by
    rw [h, Complex.neg_im, Complex.inv_im, neg_div, neg_neg]
    exact div_pos hm (Complex.normSq_pos.mpr hne)
  have : (a + msc z' + z').im = a.im + (msc z' + z').im := by
    simp only [Complex.add_im]; ring
  linarith

private lemma step1_msc_sub_mul_im_le {a z z' : ℂ} (ha : a * (a + z) = -1)
    (hz' : 0 < z'.im) : ‖msc z' - a‖ * a.im ≤ ‖z' - z‖ * ‖a‖ := by
  have h1 : a.im ≤ ‖a + msc z' + z'‖ :=
    (step1_im_le_denom a hz').trans ((le_abs_self _).trans (Complex.abs_im_le_norm _))
  calc ‖msc z' - a‖ * a.im ≤ ‖msc z' - a‖ * ‖a + msc z' + z'‖ :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ = ‖z' - z‖ * ‖a‖ := by
        rw [← norm_mul, step1_quad_diff ha z', norm_neg, norm_mul]

private lemma step1_msc_lip {z z' : ℂ} (hz : 0 < z.im) (hz' : 0 < z'.im) :
    ‖msc z' - msc z‖ * (msc z).im ≤ ‖z' - z‖ := by
  refine (step1_msc_sub_mul_im_le (msc_mul z) hz').trans ?_
  exact mul_le_of_le_one_right (norm_nonneg _) (norm_msc_lt_one hz).le

/-- **Bulk lower bound**: `Im m_sc(z) ≥ κ'/12` for `|Re z| ≤ 2 - κ'/2`, `0 < Im z ≤ 3`. -/
private lemma step1_msc_im_ge {κ' : ℝ} (hκ0 : 0 < κ') (hκ1 : κ' ≤ 1) {z : ℂ}
    (hre : |z.re| ≤ 2 - κ' / 2) (him0 : 0 < z.im) (him1 : z.im ≤ 3) :
    κ' / 12 ≤ (msc z).im := by
  set a := msc z with ha_def
  have hapos : 0 < a.im := msc_im_pos him0
  have hne : a ≠ 0 := fun h0 => by rw [h0, Complex.zero_im] at hapos; exact lt_irrefl _ hapos
  have hnz : ‖z‖ ≤ 5 := by
    have := Complex.norm_le_abs_re_add_abs_im z
    rw [abs_of_pos him0] at this
    have h2 : |z.re| ≤ 2 := by linarith
    linarith
  set R := Complex.normSq a with hR_def
  have hRpos : 0 < R := Complex.normSq_pos.mpr hne
  have hR : (1 : ℝ) / 36 ≤ R := by
    have h1 := lemT_ge him0
    unfold lemT at h1
    rw [hR_def, Complex.normSq_eq_norm_sq]
    have h2 : ((1 + 5 : ℝ) ^ 2)⁻¹ ≤ ((1 + ‖z‖) ^ 2)⁻¹ :=
      inv_anti₀ (by positivity) (by nlinarith [norm_nonneg z])
    calc (1 : ℝ) / 36 = ((1 + 5 : ℝ) ^ 2)⁻¹ := by norm_num
      _ ≤ ((1 + ‖z‖) ^ 2)⁻¹ := h2
      _ ≤ ‖msc z‖ ^ 2 := h1
  have hre_rel : z.re * R = -(a.re * (R + 1)) := by
    have h := congrArg Complex.re (msc_add_eq_neg_inv him0)
    simp only [Complex.add_re, Complex.neg_re, Complex.inv_re] at h
    rw [← ha_def, ← hR_def] at h
    field_simp at h
    linear_combination h
  have hsq : z.re ^ 2 * R ^ 2 = a.re ^ 2 * (R + 1) ^ 2 := by
    have := congrArg (· ^ 2) hre_rel
    linear_combination this
  have hx : a.re ^ 2 * (4 * R) ≤ z.re ^ 2 * R ^ 2 := by
    rw [hsq]
    have : 4 * R ≤ (R + 1) ^ 2 := by nlinarith [sq_nonneg (R - 1)]
    exact mul_le_mul_of_nonneg_left this (sq_nonneg _)
  have hx2 : a.re ^ 2 * 4 ≤ z.re ^ 2 * R := by
    have h := hx
    have : a.re ^ 2 * (4 * R) = (a.re ^ 2 * 4) * R := by ring
    rw [this, show z.re ^ 2 * R ^ 2 = (z.re ^ 2 * R) * R by ring] at h
    exact le_of_mul_le_mul_right h hRpos
  have hzre2 : z.re ^ 2 ≤ (2 - κ' / 2) ^ 2 := by
    have h0 : 0 ≤ |z.re| := abs_nonneg _
    have := mul_le_mul hre hre h0 (by linarith)
    rw [← sq, sq_abs] at this
    simpa [sq] using this
  have hRdef : R = a.re ^ 2 + a.im ^ 2 := by
    rw [hR_def, Complex.normSq_apply]; ring
  have hy2 : κ' ^ 2 / 144 ≤ a.im ^ 2 := by
    have h1 : a.re ^ 2 * 4 ≤ (2 - κ' / 2) ^ 2 * R :=
      hx2.trans (mul_le_mul_of_nonneg_right hzre2 hRpos.le)
    have h2 : R * (κ' / 4) ≤ a.im ^ 2 := by nlinarith
    have h3 : κ' / 144 ≤ R * (κ' / 4) := by nlinarith
    nlinarith
  by_contra hcon
  push Not at hcon
  have : a.im ^ 2 < (κ' / 12) ^ 2 := by
    have := mul_lt_mul'' hcon hcon hapos.le hapos.le
    nlinarith
  nlinarith

/-- **`cBulk κ = min κ 1 / 960`**, half the bulk lower bound.  Derivation: `κ'/12` (`κ' = min κ 1`)
is the proved bulk lower bound of `Im m_sc` on `|Re z| ≤ 2 - κ/2`, `0 < Im z ≤ 1`; after the
local-law and grid errors (`≤ κ'/24`) one keeps `κ'/24` for `η ≤ 1/2`, and the monotonicity of
`η ↦ η · Im m(E + iη)` extends it to the whole window `η ∈ [g, 10]` of [51, Def. 2.1] as
`κ'/480`; `cBulk` is half of that.  The literal infimum of `Im m_sc` cannot be used: every
regular `v` has `c ≤ Im m_v(10 i) ≤ 1/10`. -/
noncomputable def cBulk (κ : ℝ) : ℝ := min κ 1 / 960

theorem Step1Regularity.cBulk_pos {κ : ℝ} (hκ : 0 < κ) : 0 < cBulk κ := by
  unfold cBulk; positivity

/-! ### Elementary deterministic Lipschitz bound and monotonicity for `stieltjesVec` -/

private lemma step1_im_le_norm_sub {a : ℝ} {z : ℂ} (hz : 0 < z.im) : z.im ≤ ‖(a : ℂ) - z‖ := by
  have h := Complex.abs_im_le_norm ((a : ℂ) - z)
  simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg] at h
  rwa [abs_of_pos hz] at h

private lemma step1_sub_ne_zero {a : ℝ} {z : ℂ} (hz : 0 < z.im) : (a : ℂ) - z ≠ 0 := fun h => by
  have := step1_im_le_norm_sub (a := a) hz
  rw [h] at this
  simp at this
  linarith

/-- **Elementary Lipschitz bound** for the finite-sum Stieltjes transform (no local law, no
holomorphic Cauchy estimate: a direct term-by-term bound). -/
private lemma step1_stieltjesVec_lip {n : Type*} [Fintype n] (v : n → ℝ) {z z' : ℂ}
    (hz : 0 < z.im) (hz' : 0 < z'.im) :
    ‖stieltjesVec v z - stieltjesVec v z'‖ ≤ ‖z - z'‖ / (z.im * z'.im) := by
  have hcard : (0 : ℝ) ≤ ((Fintype.card n : ℕ) : ℝ)⁻¹ := by positivity
  have hdiff : stieltjesVec v z - stieltjesVec v z' =
      ((Fintype.card n : ℕ) : ℂ)⁻¹ *
        ∑ i, (z - z') * (((v i : ℂ) - z)⁻¹ * ((v i : ℂ) - z')⁻¹) := by
    unfold stieltjesVec
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 := step1_sub_ne_zero (a := v i) hz
    have h2 := step1_sub_ne_zero (a := v i) hz'
    field_simp
    ring
  have hterm : ∀ i : n, ‖(z - z') * (((v i : ℂ) - z)⁻¹ * ((v i : ℂ) - z')⁻¹)‖ ≤
      ‖z - z'‖ * (z.im * z'.im)⁻¹ := by
    intro i
    rw [norm_mul, norm_mul, norm_inv, norm_inv]
    have h1 := step1_im_le_norm_sub (a := v i) hz
    have h2 := step1_im_le_norm_sub (a := v i) hz'
    have hz0 : (0 : ℝ) < ‖(v i : ℂ) - z‖ := lt_of_lt_of_le hz h1
    have hz0' : (0 : ℝ) < ‖(v i : ℂ) - z'‖ := lt_of_lt_of_le hz' h2
    rw [mul_inv]
    gcongr
  have hsum : ‖∑ i, (z - z') * (((v i : ℂ) - z)⁻¹ * ((v i : ℂ) - z')⁻¹)‖ ≤
      (Fintype.card n : ℝ) * (‖z - z'‖ * (z.im * z'.im)⁻¹) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i, ‖(z - z') * (((v i : ℂ) - z)⁻¹ * ((v i : ℂ) - z')⁻¹)‖
        ≤ ∑ _i : n, ‖z - z'‖ * (z.im * z'.im)⁻¹ := Finset.sum_le_sum fun i _ => hterm i
      _ = (Fintype.card n : ℝ) * (‖z - z'‖ * (z.im * z'.im)⁻¹) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hdiff, norm_mul, norm_inv, Complex.norm_natCast]
  rcases Nat.eq_zero_or_pos (Fintype.card n) with hc0 | hcpos
  · rw [hc0]; simp; positivity
  have hcardpos : (0 : ℝ) < (Fintype.card n : ℝ) := by exact_mod_cast hcpos
  rw [div_eq_inv_mul]
  calc (Fintype.card n : ℝ)⁻¹ *
      ‖∑ i, (z - z') * (((v i : ℂ) - z)⁻¹ * ((v i : ℂ) - z')⁻¹)‖
      ≤ (Fintype.card n : ℝ)⁻¹ * ((Fintype.card n : ℝ) * (‖z - z'‖ * (z.im * z'.im)⁻¹)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (z.im * z'.im)⁻¹ * ‖z - z'‖ := by field_simp

/-- **Crude upper bound** `‖stieltjesVec v z‖ ≤ 1/Im z`, valid for every `v`. -/
private lemma step1_stieltjesVec_norm_le {n : Type*} [Fintype n] (v : n → ℝ) {z : ℂ}
    (hz : 0 < z.im) : ‖stieltjesVec v z‖ ≤ z.im⁻¹ := by
  have hterm : ∀ i : n, ‖((v i : ℂ) - z)⁻¹‖ ≤ z.im⁻¹ := fun i => by
    rw [norm_inv]
    exact inv_anti₀ hz (step1_im_le_norm_sub hz)
  unfold stieltjesVec
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  rcases Nat.eq_zero_or_pos (Fintype.card n) with hc0 | hcpos
  · rw [hc0]; simp; exact hz.le
  have hcardpos : (0 : ℝ) < (Fintype.card n : ℝ) := by exact_mod_cast hcpos
  calc (Fintype.card n : ℝ)⁻¹ * ‖∑ i, ((v i : ℂ) - z)⁻¹‖
      ≤ (Fintype.card n : ℝ)⁻¹ * ∑ i, ‖((v i : ℂ) - z)⁻¹‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ (Fintype.card n : ℝ)⁻¹ * ∑ _i : n, z.im⁻¹ :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hterm i) (by positivity)
    _ = z.im⁻¹ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp

/-- **Monotonicity of `η ↦ η · Im m(E + iη)`**, for the finite-sum Stieltjes transform of any
`v` (elementary, no local law): each term `η²/((v_i - E)² + η²)` is nondecreasing in `η ≥ 0`. -/
private lemma step1_stieltjesVec_im_mono {n : Type*} [Fintype n] (v : n → ℝ) (E : ℝ)
    {η₁ η₂ : ℝ} (hη₁ : 0 < η₁) (hη₂ : η₁ ≤ η₂) :
    η₁ * (stieltjesVec v ⟨E, η₁⟩).im ≤ η₂ * (stieltjesVec v ⟨E, η₂⟩).im := by
  have hform : ∀ η : ℝ, 0 < η →
      η * (stieltjesVec v ⟨E, η⟩).im =
        ((Fintype.card n : ℕ) : ℝ)⁻¹ * ∑ i, η ^ 2 / ((v i - E) ^ 2 + η ^ 2) := by
    intro η hη
    have hcalc : (stieltjesVec v (⟨E, η⟩ : ℂ)).im =
        ((Fintype.card n : ℕ) : ℝ)⁻¹ * ∑ i, η / ((v i - E) ^ 2 + η ^ 2) := by
      unfold stieltjesVec
      rw [show (((Fintype.card n : ℕ) : ℂ))⁻¹ = ((((Fintype.card n : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) by
        rw [Complex.ofReal_inv, Complex.ofReal_natCast], Complex.im_ofReal_mul, Complex.im_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Complex.inv_im, Complex.sub_im, Complex.ofReal_im]
      have hne : Complex.normSq ((v i : ℂ) - (⟨E, η⟩ : ℂ)) = (v i - E) ^ 2 + η ^ 2 := by
        rw [Complex.normSq_apply]; simp; ring
      rw [hne]
      ring
    rw [hcalc, mul_left_comm, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hform η₁ hη₁, hform η₂ (lt_of_lt_of_le hη₁ hη₂)]
  have hpos : (0 : ℝ) ≤ ((Fintype.card n : ℕ) : ℝ)⁻¹ := by positivity
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) hpos
  have hη2pos : (0 : ℝ) < η₂ := lt_of_lt_of_le hη₁ hη₂
  have hden1 : (0 : ℝ) < (v i - E) ^ 2 + η₁ ^ 2 := by positivity
  have hden2 : (0 : ℝ) < (v i - E) ^ 2 + η₂ ^ 2 := by positivity
  rw [div_le_div_iff₀ hden1 hden2]
  nlinarith [sq_nonneg (v i - E), sq_nonneg (η₁ - η₂), mul_le_mul hη₂ hη₂ hη₁.le hη2pos.le]

/-! ### The uniform-in-`z` upgrade of `hLL`

`RBM.eventually_forall_of_forall_sequences` converts `BandTracialLocalLaw`'s "for every
admissible deterministic sequence `z`, eventually" statement into a single eventual index valid
for **every** `z` in the domain simultaneously (at each large `N`), which is what a grid-based
union bound needs. -/

private theorem step1_conv_eventually_le_one {a : ℝ} (ha : a ≤ 0) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ a ≤ 1 := by
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  exact Real.rpow_le_one_of_one_le_of_nonpos hN1 ha

private theorem step1_uniform_of_hLL (d : Dims) {κ : ℝ} (hLL : BandTracialLocalLaw d κ)
    (hκ2 : κ ≤ 2) {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) {τ' D : ℝ} (hτ' : 0 < τ') (hD : 0 < D) :
    ∀ᶠ N : ℕ in atTop, ∀ z : ℂ, 0 < z.im → z.im ≤ 1 → |z.re| ≤ 2 - κ →
      (N : ℝ) ^ (-1 + τ) ≤ z.im →
      (Gauss.band d).P {ω | ((Gauss.band d).W N : ℝ) ^ τ' * ((Gauss.band d).zScale N z)⁻¹ <
          ‖RBM.stieltjes (Xmat d N ω) z - msc z‖} ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
  have hb0 : ∀ n : ℕ, (0 : ℝ) < (⟨0, 1⟩ : ℂ).im ∧ (⟨0, 1⟩ : ℂ).im ≤ 1 ∧
      |(⟨0, 1⟩ : ℂ).re| ≤ 2 - κ := fun _ => ⟨one_pos, le_refl 1, by simpa using hκ2⟩
  have hb1 : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (-1 + τ) ≤ (⟨0, 1⟩ : ℂ).im := by
    simpa using step1_conv_eventually_le_one (a := -1 + τ) (by linarith)
  have hseq : ∀ f : ℕ → ℂ,
      (∀ n, (0 : ℝ) < (f n).im ∧ (f n).im ≤ 1 ∧ |(f n).re| ≤ 2 - κ) →
      (∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (-1 + τ) ≤ (f n).im) →
      ∀ᶠ n : ℕ in atTop, (Gauss.band d).P
          {ω | ((Gauss.band d).W n : ℝ) ^ τ' * ((Gauss.band d).zScale n (f n))⁻¹ <
            ‖RBM.stieltjes (Xmat d n ω) (f n) - msc (f n)‖} ≤ ENNReal.ofReal ((n : ℝ) ^ (-D)) := by
    intro f hf0 hf1
    have hconv := hLL τ hτ0 f (fun n => (hf0 n).1) (fun n => (hf0 n).2.1) (fun n => (hf0 n).2.2)
      hf1 τ' hτ' D hD
    filter_upwards [hconv] with n hn
    have heq : {ω | ((Gauss.band d).W n : ℝ) ^ τ' * ((Gauss.band d).zScale n (f n))⁻¹ <
          ‖RBM.stieltjes (Xmat d n ω) (f n) - msc (f n)‖} =
        {ω | ∃ _u : Unit, ((Gauss.band d).W n : ℝ) ^ τ' * ((Gauss.band d).zScale n (f n))⁻¹ <
          ‖(((Gauss.band d).L n * (Gauss.band d).W n : ℕ) : ℂ)⁻¹ *
              (green (Xmat d n ω) (f n)).trace - msc (f n)‖} := by
      ext ω
      have hcard : (((Gauss.band d).L n * (Gauss.band d).W n : ℕ) : ℂ) =
          ((Fintype.card (d.Idx n) : ℕ) : ℂ) := by
        norm_cast
        simp [ZMod.card]
      simp only [Set.mem_ofPred_eq]
      rw [RBM.stieltjes, hcard]
      exact ⟨fun h => ⟨(), h⟩, fun ⟨_, h⟩ => h⟩
    rw [heq]
    exact hn
  simpa using RBM.eventually_forall_of_forall_sequences
    (fun n z => (0 : ℝ) < z.im ∧ z.im ≤ 1 ∧ |z.re| ≤ 2 - κ)
    (fun n z => (n : ℝ) ^ (-1 + τ) ≤ z.im)
    (fun n z => (Gauss.band d).P
        {ω | ((Gauss.band d).W n : ℝ) ^ τ' * ((Gauss.band d).zScale n z)⁻¹ <
          ‖RBM.stieltjes (Xmat d n ω) z - msc z‖} ≤ ENNReal.ofReal ((n : ℝ) ^ (-D)))
    (fun _ => (⟨0, 1⟩ : ℂ)) hb0 hb1 hseq

/-! ### The OU flow rescaling: `a = e^{-t/2} = √s`, `s = 1 - ζ(t)` -/

private theorem step1_ouBandCoeff_eq_sqrt {t : ℝ} :
    ouBandCoeff t = Real.sqrt (1 - ouZeta t) := by
  unfold ouBandCoeff ouZeta
  rw [show (1 : ℝ) - (1 - Real.exp (-t)) = Real.exp (-t/2) * Real.exp (-t/2) by
    rw [← Real.exp_add]; ring_nf,
    Real.sqrt_mul_self (Real.exp_pos _).le]

private theorem step1_ouBandCoeff_pos (t : ℝ) : 0 < ouBandCoeff t := Real.exp_pos _

/-- `1 - t/2 ≤ e^{-t/2}` (from `1 + x ≤ e^x` at `x = -t/2`). -/
private theorem step1_ouBandCoeff_ge {t : ℝ} : 1 - t / 2 ≤ ouBandCoeff t := by
  have h := Real.add_one_le_exp (-t / 2)
  unfold ouBandCoeff
  have he : -t / 2 = -(t / 2) := by ring
  rw [he] at h ⊢
  linarith

/-- `(e^{-t/2})⁻¹ ≤ 1 + 2t` for `0 ≤ t ≤ 1`. -/
private theorem step1_ouBandCoeff_inv_le {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (ouBandCoeff t)⁻¹ ≤ 1 + 2 * t := by
  have h1 : (0 : ℝ) < 1 - t / 2 := by linarith
  have h2 : 1 - t / 2 ≤ ouBandCoeff t := step1_ouBandCoeff_ge
  have h3 : (ouBandCoeff t)⁻¹ ≤ (1 - t / 2)⁻¹ := inv_anti₀ h1 h2
  refine h3.trans ?_
  rw [inv_le_iff_one_le_mul₀ h1]
  nlinarith

/-! ### The `vOU` ↔ `stieltjes(Xmat, ·)` affine identity -/

/-- `stieltjesVec (vOU d N τs E₀ ω) w = a⁻¹ · stieltjes(Xmat d N ω, a⁻¹(w + E₀))`,
`a = ouBandCoeff (tPow τs N)`. -/
private theorem step1_vOU_stieltjesVec_eq (d : Dims) (N : ℕ) (τs E₀ : ℝ) (ω : Ω d) {w : ℂ}
    (hw : 0 < w.im) :
    stieltjesVec (vOU d N τs E₀ ω) w =
      ((ouBandCoeff ((Gauss.band d).tPow τs N) : ℝ) : ℂ)⁻¹ *
        RBM.stieltjes (Xmat d N ω)
          (((ouBandCoeff ((Gauss.band d).tPow τs N) : ℝ) : ℂ)⁻¹ * (w + E₀)) := by
  set a : ℝ := ouBandCoeff ((Gauss.band d).tPow τs N) with ha_def
  have hapos : 0 < a := step1_ouBandCoeff_pos _
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hapos.ne'
  have hz : 0 < (((a : ℝ) : ℂ)⁻¹ * (w + E₀)).im := by
    rw [Complex.mul_im, Complex.inv_re, Complex.inv_im, Complex.ofReal_re, Complex.ofReal_im]
    simp only [zero_div, neg_zero, zero_mul, sub_zero, Complex.normSq_ofReal]
    rw [Complex.add_im, Complex.ofReal_im, add_zero]
    positivity
  rw [step1_stieltjes_eq_stieltjesVec (Xmat_isHermitian d N ω) hz]
  unfold stieltjesVec vOU
  rw [mul_left_comm]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  set lami : ℝ := (Xmat_isHermitian d N ω).eigenvalues i with hlam_def
  have hkey : ((a : ℝ) : ℂ) * lami - (E₀ : ℂ) - w =
      (a : ℂ) * ((lami : ℂ) - (((a : ℝ) : ℂ)⁻¹ * (w + E₀))) := by
    rw [mul_sub]
    rw [show (a : ℂ) * (((a : ℝ) : ℂ)⁻¹ * (w + E₀)) = w + E₀ by field_simp]
    ring
  rw [show ((a * lami - E₀ : ℝ) : ℂ) - w = ((a : ℝ) : ℂ) * lami - (E₀ : ℂ) - w by push_cast; ring,
    hkey, mul_inv]

/-! ### The `z`-domain fitting a `β`-window around `E₀` -/

/-- If `|E₀| ≤ 2 - κ`, `|β| ≤ κ'/16` (`κ' = min κ 1`) and `0 ≤ t ≤ 7κ/96`, then
`(1 + 2t)|β + E₀| ≤ 2 - κ/2`. -/
private theorem step1_re_z_bound {κ t E₀ β : ℝ} (hκ0 : 0 < κ) (hκ2 : κ ≤ 2)
    (hE₀ : |E₀| ≤ 2 - κ) (hβ : |β| ≤ min κ 1 / 16) (ht0 : 0 ≤ t) (ht : t ≤ 7 * κ / 96) :
    (1 + 2 * t) * |β + E₀| ≤ 2 - κ / 2 := by
  have hκ' : min κ 1 ≤ κ := min_le_left _ _
  have hβ' : |β| ≤ κ / 16 := hβ.trans (by linarith)
  have h1 : |β + E₀| ≤ κ / 16 + (2 - κ) := (abs_add_le _ _).trans (by linarith)
  have h2 : (0 : ℝ) ≤ κ / 16 + (2 - κ) := by linarith
  calc (1 + 2 * t) * |β + E₀| ≤ (1 + 2 * t) * (κ / 16 + (2 - κ)) :=
        mul_le_mul_of_nonneg_left h1 (by linarith)
    _ ≤ 2 - κ / 2 := by nlinarith

/-! ### `t_* = M^{-1+τ_*} → 0` -/

private theorem step1_tPow_pos (d : Dims) (τs : ℝ) (N : ℕ) : 0 < (Gauss.band d).tPow τs N := by
  unfold Band.tPow
  have h1 : (0 : ℝ) < ((Gauss.band d).size N : ℝ) := by
    have := (Gauss.band d).one_le_size N
    exact_mod_cast lt_of_lt_of_le one_pos this
  exact Real.rpow_pos_of_pos h1 _

private theorem step1_tPow_tendsto_zero (d : Dims) {τs : ℝ} (h1 : τs < 1) :
    Tendsto (fun N : ℕ => (Gauss.band d).tPow τs N) atTop (𝓝 0) := by
  unfold Band.tPow
  have hsize : Tendsto (fun N : ℕ => (((Gauss.band d).size N : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (Gauss.band d).tendsto_size
  have hr := tendsto_rpow_neg_atTop (y := 1 - τs) (by linarith)
  have heq : (fun x : ℝ => x ^ (-(1 - τs))) = (fun x : ℝ => x ^ (-1 + τs)) := by
    funext x; congr 1; ring
  rw [heq] at hr
  exact hr.comp hsize

private theorem step1_tPow_eventually_le (d : Dims) {τs c : ℝ} (h1 : τs < 1) (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop, (Gauss.band d).tPow τs N ≤ c := by
  filter_upwards [(step1_tPow_tendsto_zero d h1).eventually (Iio_mem_nhds hc)] with N hN
  exact hN.le

/-! ### A robust lower bound on `zScale`: `zScale ≥ min (W √η, M η)` -/

private theorem step1_zScale_ge (d : Dims) (N : ℕ) {z : ℂ} (hz : 0 < z.im) :
    min (((Gauss.band d).W N : ℝ) * Real.sqrt z.im) (msize d N * z.im) ≤
      (Gauss.band d).zScale N z := by
  have hW : (0 : ℝ) ≤ ((Gauss.band d).W N : ℝ) := Nat.cast_nonneg _
  have hstep1 : min (1 / Real.sqrt z.im) ((Gauss.band d).L N : ℝ) * z.im ≤
      (min (1 / Real.sqrt z.im) ((Gauss.band d).L N : ℝ) + 1) * z.im :=
    mul_le_mul_of_nonneg_right (by linarith) hz.le
  have hstep3 : (1 / Real.sqrt z.im) * z.im = Real.sqrt z.im := by
    rw [div_mul_eq_mul_div, one_mul, Real.div_sqrt]
  have hML : msize d N = ((Gauss.band d).W N : ℝ) * ((Gauss.band d).L N : ℝ) := by
    have hcardL : ((Gauss.band d).L N : ℝ) = (d.L N : ℝ) := by rw [band_L]
    have hcardW : ((Gauss.band d).W N : ℝ) = (d.W N : ℝ) := by rw [band_W]
    unfold msize ouMatrixSize
    rw [hcardL, hcardW]; push_cast; ring
  calc min (((Gauss.band d).W N : ℝ) * Real.sqrt z.im) (msize d N * z.im)
      = min (((Gauss.band d).W N : ℝ) * ((1 / Real.sqrt z.im) * z.im))
          (((Gauss.band d).W N : ℝ) * (((Gauss.band d).L N : ℝ) * z.im)) := by
        rw [hstep3, hML]; ring_nf
    _ = ((Gauss.band d).W N : ℝ) * min ((1 / Real.sqrt z.im) * z.im)
          (((Gauss.band d).L N : ℝ) * z.im) := (mul_min_of_nonneg _ _ hW).symm
    _ = ((Gauss.band d).W N : ℝ) *
          (min (1 / Real.sqrt z.im) ((Gauss.band d).L N : ℝ) * z.im) := by
        rw [min_mul_of_nonneg _ _ hz.le]
    _ ≤ ((Gauss.band d).W N : ℝ) *
          ((min (1 / Real.sqrt z.im) ((Gauss.band d).L N : ℝ) + 1) * z.im) :=
        mul_le_mul_of_nonneg_left hstep1 hW
    _ = (Gauss.band d).zScale N z := by unfold Band.zScale ellZ ellOf; ring

/-- `M^{1/2+c} ≤ W` eventually, from `(2.2)` and `M ≤ N`. -/
private theorem step1_W_ge_msize_rpow (d : Dims) :
    ∀ᶠ N : ℕ in atTop, (msize d N) ^ (1 / 2 + d.c) ≤ ((Gauss.band d).W N : ℝ) := by
  filter_upwards [d.dim, d.bandwidth] with N hdim hbw
  have hM_le_N : msize d N ≤ (N : ℝ) := by
    unfold msize ouMatrixSize
    have : d.L N * d.W N = d.W N * d.L N := by ring
    rw [this]
    exact_mod_cast hdim.1
  have hWN : ((Gauss.band d).W N : ℝ) = (d.W N : ℝ) := by rw [band_W]
  rw [hWN]
  have hMnn : (0 : ℝ) ≤ msize d N := by unfold msize; positivity
  calc (msize d N) ^ (1 / 2 + d.c) ≤ (N : ℝ) ^ (1 / 2 + d.c) :=
        Real.rpow_le_rpow hMnn hM_le_N (by linarith [d.c_pos])
    _ ≤ (d.W N : ℝ) := hbw

/-- The local-law error bound `W^τ' zScale⁻¹` is at most `max` of two elementary terms. -/
private theorem step1_error_le (d : Dims) (N : ℕ) {z : ℂ} (hz : 0 < z.im) {τ' : ℝ} :
    ((Gauss.band d).W N : ℝ) ^ τ' * ((Gauss.band d).zScale N z)⁻¹ ≤
      max (((Gauss.band d).W N : ℝ) ^ (τ' - 1) * (Real.sqrt z.im)⁻¹)
        (((Gauss.band d).W N : ℝ) ^ τ' * (msize d N * z.im)⁻¹) := by
  have hW0 : (0 : ℝ) < ((Gauss.band d).W N : ℝ) := by
    exact_mod_cast (Gauss.band d).W_pos N
  have hA : (0 : ℝ) < ((Gauss.band d).W N : ℝ) * Real.sqrt z.im :=
    mul_pos hW0 (Real.sqrt_pos.mpr hz)
  have hMpos : (0 : ℝ) < msize d N := by
    have hL := d.three_le_L N
    have hW := d.W_pos N
    unfold msize ouMatrixSize
    have : 0 < d.L N * d.W N := Nat.mul_pos (by omega) hW
    exact_mod_cast this
  have hB : (0 : ℝ) < msize d N * z.im := mul_pos hMpos hz
  have hmin := step1_zScale_ge d N hz
  have hinv : ((Gauss.band d).zScale N z)⁻¹ ≤
      max (((Gauss.band d).W N : ℝ) * Real.sqrt z.im)⁻¹ (msize d N * z.im)⁻¹ := by
    rcases le_total (((Gauss.band d).W N : ℝ) * Real.sqrt z.im) (msize d N * z.im) with h | h
    · rw [min_eq_left h] at hmin
      exact le_trans (inv_anti₀ hA hmin) (le_max_left _ _)
    · rw [min_eq_right h] at hmin
      exact le_trans (inv_anti₀ hB hmin) (le_max_right _ _)
  have hWτ' : (0 : ℝ) ≤ ((Gauss.band d).W N : ℝ) ^ τ' := Real.rpow_nonneg hW0.le _
  calc ((Gauss.band d).W N : ℝ) ^ τ' * ((Gauss.band d).zScale N z)⁻¹ ≤
      ((Gauss.band d).W N : ℝ) ^ τ' *
        max (((Gauss.band d).W N : ℝ) * Real.sqrt z.im)⁻¹ (msize d N * z.im)⁻¹ :=
        mul_le_mul_of_nonneg_left hinv hWτ'
    _ = max (((Gauss.band d).W N : ℝ) ^ τ' * (((Gauss.band d).W N : ℝ) * Real.sqrt z.im)⁻¹)
          (((Gauss.band d).W N : ℝ) ^ τ' * (msize d N * z.im)⁻¹) :=
        mul_max_of_nonneg _ _ hWτ'
    _ = max (((Gauss.band d).W N : ℝ) ^ (τ' - 1) * (Real.sqrt z.im)⁻¹)
          (((Gauss.band d).W N : ℝ) ^ τ' * (msize d N * z.im)⁻¹) := by
        congr 1
        rw [mul_inv, ← mul_assoc, Real.rpow_sub hW0, Real.rpow_one]
        field_simp

/-- `W^τ' (M η)⁻¹ ≤ M^{τ' - ρ}` for `η ≥ M^{-1+ρ}` (using `W ≤ M`, no bandwidth needed). -/
private theorem step1_term2_le (d : Dims) (N : ℕ) {z : ℂ} {τ' ρ : ℝ} (hτ' : 0 ≤ τ')
    (hη : (msize d N) ^ (-1 + ρ) ≤ z.im) :
    ((Gauss.band d).W N : ℝ) ^ τ' * (msize d N * z.im)⁻¹ ≤ (msize d N) ^ (τ' - ρ) := by
  have hL := d.three_le_L N
  have hWp := d.W_pos N
  have hMpos : (0 : ℝ) < msize d N := by
    unfold msize ouMatrixSize
    have : 0 < d.L N * d.W N := Nat.mul_pos (by omega) hWp
    exact_mod_cast this
  have hWM : ((Gauss.band d).W N : ℝ) ≤ msize d N := by
    have hWN : ((Gauss.band d).W N : ℝ) = (d.W N : ℝ) := by rw [band_W]
    rw [hWN]
    unfold msize ouMatrixSize
    have : (d.W N : ℕ) ≤ d.L N * d.W N := Nat.le_mul_of_pos_left _ (by omega)
    exact_mod_cast this
  have hηpos : (0 : ℝ) < z.im :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos hMpos _) hη
  have h1 : ((Gauss.band d).W N : ℝ) ^ τ' ≤ (msize d N) ^ τ' :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hWM hτ'
  have h2 : (0 : ℝ) < msize d N * (msize d N) ^ (-1 + ρ) :=
    mul_pos hMpos (Real.rpow_pos_of_pos hMpos _)
  have h3 : msize d N * (msize d N) ^ (-1 + ρ) ≤ msize d N * z.im :=
    mul_le_mul_of_nonneg_left hη hMpos.le
  calc ((Gauss.band d).W N : ℝ) ^ τ' * (msize d N * z.im)⁻¹ ≤
      (msize d N) ^ τ' * (msize d N * (msize d N) ^ (-1 + ρ))⁻¹ :=
        mul_le_mul h1 (inv_anti₀ h2 h3) (by positivity) (Real.rpow_nonneg hMpos.le _)
    _ = (msize d N) ^ (τ' - ρ) := by
        rw [show msize d N * (msize d N) ^ (-1 + ρ) = (msize d N) ^ (1 : ℝ) *
            (msize d N) ^ (-1 + ρ) by rw [Real.rpow_one],
          ← Real.rpow_add hMpos, ← Real.rpow_neg hMpos.le, ← Real.rpow_add hMpos]
        ring_nf

/-- `W^{τ'-1} (√η)⁻¹ ≤ M^{(1/2+c)(τ'-1) + (1-ρ)/2}` for `η ≥ M^{-1+ρ}`, using
`M^{1/2+c} ≤ W` (bandwidth). -/
private theorem step1_term1_le (d : Dims) (N : ℕ) {z : ℂ} {τ' ρ : ℝ} (hτ'1 : τ' < 1)
    (hW : (msize d N) ^ (1 / 2 + d.c) ≤ ((Gauss.band d).W N : ℝ))
    (hη : (msize d N) ^ (-1 + ρ) ≤ z.im) :
    ((Gauss.band d).W N : ℝ) ^ (τ' - 1) * (Real.sqrt z.im)⁻¹ ≤
      (msize d N) ^ ((1 / 2 + d.c) * (τ' - 1) + (1 - ρ) / 2) := by
  have hL := d.three_le_L N
  have hWp := d.W_pos N
  have hMpos : (0 : ℝ) < msize d N := by
    unfold msize ouMatrixSize
    have : 0 < d.L N * d.W N := Nat.mul_pos (by omega) hWp
    exact_mod_cast this
  have hMWpos : (0 : ℝ) < (msize d N) ^ (1 / 2 + d.c) := Real.rpow_pos_of_pos hMpos _
  have hηpos : (0 : ℝ) < z.im :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos hMpos _) hη
  have h1 : ((Gauss.band d).W N : ℝ) ^ (τ' - 1) ≤ ((msize d N) ^ (1 / 2 + d.c)) ^ (τ' - 1) :=
    Real.rpow_le_rpow_of_nonpos hMWpos hW (by linarith)
  have h2 : (Real.sqrt z.im)⁻¹ ≤ ((msize d N) ^ (-1 + ρ)) ^ (-(1 / 2) : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hηpos.le]
    exact Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hMpos _) hη (by norm_num)
  calc ((Gauss.band d).W N : ℝ) ^ (τ' - 1) * (Real.sqrt z.im)⁻¹ ≤
      ((msize d N) ^ (1 / 2 + d.c)) ^ (τ' - 1) * ((msize d N) ^ (-1 + ρ)) ^ (-(1 / 2) : ℝ) :=
        mul_le_mul h1 h2 (by positivity) (Real.rpow_nonneg (Real.rpow_pos_of_pos hMpos _).le _)
    _ = (msize d N) ^ ((1 / 2 + d.c) * (τ' - 1) + (1 - ρ) / 2) := by
        rw [← Real.rpow_mul hMpos.le, ← Real.rpow_mul hMpos.le, ← Real.rpow_add hMpos]
        ring_nf

/-! ### The `M^{-3}`-grid: `β ∈ [-κ'/16, κ'/16]`, `η ∈ [g(N), 1/2]` -/

/-- The number of `β`-grid intervals, dense enough (`≥ (κ'/8) M^3`) for `M^{-3}`-interpolation. -/
private noncomputable def step1_bC (κ : ℝ) (M : ℝ) : ℕ := ⌈(min κ 1 / 8) * M ^ 3⌉₊ + 1

/-- The number of `η`-grid intervals, dense enough (`≥ (1/2) M^3`). -/
private noncomputable def step1_hC (M : ℝ) : ℕ := ⌈(1 / 2 : ℝ) * M ^ 3⌉₊ + 1

private theorem step1_bC_pos (κ M : ℝ) : 0 < step1_bC κ M := Nat.succ_pos _

private theorem step1_hC_pos (M : ℝ) : 0 < step1_hC M := Nat.succ_pos _

/-- The `β`-grid point, always in `[-κ'/16, κ'/16]`. -/
private noncomputable def step1_betaGrid (κ M : ℝ) (p : Fin (step1_bC κ M + 1)) : ℝ :=
  -(min κ 1 / 16) + (p : ℝ) / (step1_bC κ M : ℝ) * (min κ 1 / 8)

/-- The `η`-grid point, always in `[g, 1/2]`. -/
private noncomputable def step1_etaGrid (M g : ℝ) (q : Fin (step1_hC M + 1)) : ℝ :=
  g + (q : ℝ) / (step1_hC M : ℝ) * (1 / 2 - g)

private theorem step1_betaGrid_mem (κ M : ℝ) (hκ : 0 < κ) (p : Fin (step1_bC κ M + 1)) :
    |step1_betaGrid κ M p| ≤ min κ 1 / 16 := by
  have hC : (0 : ℝ) < (step1_bC κ M : ℝ) := by exact_mod_cast step1_bC_pos κ M
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg _
  have hp1 : (p : ℝ) ≤ (step1_bC κ M : ℝ) := by exact_mod_cast (Nat.lt_succ_iff.mp p.isLt)
  have hfrac0 : (0 : ℝ) ≤ (p : ℝ) / (step1_bC κ M : ℝ) := by positivity
  have hfrac1 : (p : ℝ) / (step1_bC κ M : ℝ) ≤ 1 := (div_le_one hC).mpr hp1
  have hκ' : (0 : ℝ) < min κ 1 := lt_min hκ one_pos
  rw [abs_le]
  unfold step1_betaGrid
  constructor <;> nlinarith [mul_le_of_le_one_left hκ'.le hfrac1,
    mul_nonneg hfrac0 hκ'.le]

private theorem step1_etaGrid_mem (M g : ℝ) (hg1 : g ≤ 1 / 2)
    (q : Fin (step1_hC M + 1)) : g ≤ step1_etaGrid M g q ∧ step1_etaGrid M g q ≤ 1 / 2 := by
  have hC : (0 : ℝ) < (step1_hC M : ℝ) := by exact_mod_cast step1_hC_pos M
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg _
  have hq1 : (q : ℝ) ≤ (step1_hC M : ℝ) := by exact_mod_cast (Nat.lt_succ_iff.mp q.isLt)
  have hfrac0 : (0 : ℝ) ≤ (q : ℝ) / (step1_hC M : ℝ) := by positivity
  have hfrac1 : (q : ℝ) / (step1_hC M : ℝ) ≤ 1 := (div_le_one hC).mpr hq1
  unfold step1_etaGrid
  constructor
  · nlinarith
  · nlinarith [mul_le_mul_of_nonneg_left hfrac1 (by linarith : (0:ℝ) ≤ 1/2 - g)]

/-- **Nearest grid point**: on an evenly-spaced `(C+1)`-point grid of `[a,b]`, every `x ∈ [a,b]`
is within `(b-a)/C` of some grid point. -/
private theorem step1_grid_exists {a b : ℝ} (hab : a < b) {C : ℕ} (hC : 0 < C) {x : ℝ}
    (hx0 : a ≤ x) (hx1 : x ≤ b) :
    ∃ k : Fin (C + 1), |x - (a + (k : ℝ) / (C : ℝ) * (b - a))| ≤ (b - a) / (C : ℝ) := by
  have hba : (0 : ℝ) < b - a := by linarith
  have hCR : (0 : ℝ) < (C : ℝ) := by exact_mod_cast hC
  set r : ℝ := (x - a) / (b - a) * (C : ℝ) with hr_def
  have hr0 : 0 ≤ r := by
    have h1 : 0 ≤ (x - a) / (b - a) := div_nonneg (by linarith) hba.le
    rw [hr_def]; positivity
  have hrC : r ≤ (C : ℝ) := by
    have h1 : (x - a) / (b - a) ≤ 1 := (div_le_one hba).mpr (by linarith)
    calc r = (x - a) / (b - a) * (C : ℝ) := hr_def
      _ ≤ 1 * (C : ℝ) := by gcongr
      _ = (C : ℝ) := one_mul _
  set k0 : ℕ := ⌊r⌋₊ with hk0_def
  have hk0C : k0 ≤ C := by
    rw [hk0_def]
    exact_mod_cast Nat.floor_le_of_le hrC
  refine ⟨⟨k0, by omega⟩, ?_⟩
  have hfl_le : (k0 : ℝ) ≤ r := Nat.floor_le hr0
  have hfl_lt : r < (k0 : ℝ) + 1 := Nat.lt_floor_add_one r
  have hxr : x = a + r / (C : ℝ) * (b - a) := by rw [hr_def]; field_simp; ring
  have heq : x - (a + (k0 : ℝ) / (C : ℝ) * (b - a)) = (r - (k0 : ℝ)) / (C : ℝ) * (b - a) := by
    rw [hxr]; field_simp; ring
  simp only [Fin.val_mk]
  rw [heq, abs_of_nonneg (mul_nonneg (div_nonneg (by linarith) hCR.le) hba.le)]
  calc (r - (k0 : ℝ)) / (C : ℝ) * (b - a) ≤ 1 / (C : ℝ) * (b - a) := by
        gcongr
        linarith
    _ = (b - a) / (C : ℝ) := by ring

private theorem step1_bC_ge (κ M : ℝ) : (min κ 1 / 8) * M ^ 3 ≤ (step1_bC κ M : ℝ) := by
  unfold step1_bC
  have h := Nat.le_ceil ((min κ 1 / 8) * M ^ 3)
  push_cast
  linarith

private theorem step1_hC_ge (M : ℝ) : (1 / 2 : ℝ) * M ^ 3 ≤ (step1_hC M : ℝ) := by
  unfold step1_hC
  have h := Nat.le_ceil ((1 / 2 : ℝ) * M ^ 3)
  push_cast
  linarith

/-- The `β`-grid spacing is at most `M^{-3}`. -/
private theorem step1_betaGrid_spacing (κ M : ℝ) (hκ : 0 < κ) (hM : 0 < M) :
    min κ 1 / 8 / (step1_bC κ M : ℝ) ≤ (M ^ 3)⁻¹ := by
  have hCpos : (0 : ℝ) < (step1_bC κ M : ℝ) := by exact_mod_cast step1_bC_pos κ M
  have hκ' : (0 : ℝ) < min κ 1 := lt_min hκ one_pos
  have hM3 : (0 : ℝ) < M ^ 3 := by positivity
  have hge := step1_bC_ge κ M
  rw [div_le_iff₀ hCpos, inv_mul_eq_div, le_div_iff₀ hM3]
  linarith

/-- The `η`-grid spacing is at most `M^{-3}`. -/
private theorem step1_etaGrid_spacing (M g : ℝ) (hM : 0 < M) (hg0 : 0 ≤ g) (hg1 : g ≤ 1 / 2) :
    (1 / 2 - g) / (step1_hC M : ℝ) ≤ (M ^ 3)⁻¹ := by
  have hCpos : (0 : ℝ) < (step1_hC M : ℝ) := by exact_mod_cast step1_hC_pos M
  have hM3 : (0 : ℝ) < M ^ 3 := by positivity
  have hge := step1_hC_ge M
  rw [div_le_iff₀ hCpos, inv_mul_eq_div, le_div_iff₀ hM3]
  nlinarith

private theorem step1_bC_le (κ M : ℝ) (hκ : 0 < κ) (hM : 0 ≤ M) :
    (step1_bC κ M : ℝ) ≤ M ^ 3 + 3 := by
  unfold step1_bC
  have hκ' : min κ 1 / 8 ≤ 1 := by
    have := min_le_right κ (1 : ℝ)
    linarith
  have h1 : (min κ 1 / 8) * M ^ 3 ≤ M ^ 3 := by nlinarith [pow_nonneg hM 3]
  have h2 : (⌈(min κ 1 / 8) * M ^ 3⌉₊ : ℝ) < (min κ 1 / 8) * M ^ 3 + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  push_cast
  linarith

private theorem step1_hC_le (M : ℝ) (hM : 0 ≤ M) : (step1_hC M : ℝ) ≤ M ^ 3 + 3 := by
  unfold step1_hC
  have h1 : (1 / 2 : ℝ) * M ^ 3 ≤ M ^ 3 := by nlinarith [pow_nonneg hM 3]
  have h2 : (⌈(1 / 2 : ℝ) * M ^ 3⌉₊ : ℝ) < (1 / 2 : ℝ) * M ^ 3 + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  push_cast
  linarith

/-- **The grid has polynomial-in-`N` size**: `card K(N) ≤ 4 (M(N)^3+3)^2 ≤ N^8` eventually. -/
private theorem step1_card_le (d : Dims) (κ : ℝ) (hκ : 0 < κ) :
    ∀ᶠ N : ℕ in atTop,
      ((Fintype.card (Fin (step1_bC κ (msize d N) + 1) × Fin (step1_hC (msize d N) + 1)) :
        ℝ)) ≤ (N : ℝ) ^ (8 : ℝ) := by
  have hMnn : ∀ N, (0 : ℝ) ≤ msize d N := fun N => by unfold msize; positivity
  have hMle : ∀ᶠ N : ℕ in atTop, msize d N ≤ (N : ℝ) := by
    filter_upwards [d.dim] with N hdim
    unfold msize ouMatrixSize
    have h : d.L N * d.W N = d.W N * d.L N := by ring
    rw [h]; exact_mod_cast hdim.1
  filter_upwards [hMle, eventually_ge_atTop 4] with N hMle hN4
  have hN4' : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN4
  have hbC := step1_bC_le κ (msize d N) hκ (hMnn N)
  have hhC := step1_hC_le (msize d N) (hMnn N)
  have hM3 : (msize d N) ^ 3 ≤ (N : ℝ) ^ 3 := by gcongr; exact hMnn N
  have hN64 : (64 : ℝ) ≤ (N : ℝ) ^ 3 := by nlinarith [sq_nonneg ((N:ℝ) - 4)]
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  have hbC' : ((step1_bC κ (msize d N) : ℝ) + 1) ≤ 2 * (N : ℝ) ^ 3 := by linarith
  have hhC' : ((step1_hC (msize d N) : ℝ) + 1) ≤ 2 * (N : ℝ) ^ 3 := by linarith
  have hcard : (((step1_bC κ (msize d N) : ℝ) + 1) * ((step1_hC (msize d N) : ℝ) + 1)) ≤
      4 * (N : ℝ) ^ 6 := by
    have hh0 : (0 : ℝ) ≤ (step1_hC (msize d N) : ℝ) + 1 := by positivity
    calc ((step1_bC κ (msize d N) : ℝ) + 1) * ((step1_hC (msize d N) : ℝ) + 1) ≤
        (2 * (N : ℝ) ^ 3) * (2 * (N : ℝ) ^ 3) :=
          mul_le_mul hbC' hhC' hh0 (by positivity)
      _ = 4 * (N : ℝ) ^ 6 := by ring
  have hN2 : (4 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
  have hfin : 4 * (N : ℝ) ^ 6 ≤ (N : ℝ) ^ 8 := by nlinarith [pow_nonneg (by linarith : (0:ℝ) ≤ (N:ℝ)) 6]
  have hgoal : (((step1_bC κ (msize d N) + 1 : ℕ) : ℝ)) *
      (((step1_hC (msize d N) + 1 : ℕ) : ℝ)) ≤ (N : ℝ) ^ 8 := by
    push_cast
    linarith [hcard, hfin]
  rw [show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, Nat.cast_mul]
  exact hgoal

/-! ### The spectral parameter `z(β,η) = a⁻¹(β + E₀ + iη)` -/

private noncomputable def step1_zAt (t E₀ β η : ℝ) : ℂ :=
  ((ouBandCoeff t : ℝ) : ℂ)⁻¹ * (⟨β + E₀, η⟩ : ℂ)

private theorem step1_zAt_re (t E₀ β η : ℝ) :
    (step1_zAt t E₀ β η).re = (β + E₀) / ouBandCoeff t := by
  unfold step1_zAt
  rw [Complex.mul_re, Complex.inv_re, Complex.inv_im, Complex.ofReal_re, Complex.ofReal_im]
  simp only [Complex.normSq_ofReal, neg_zero, zero_div, zero_mul, sub_zero]
  field_simp

private theorem step1_zAt_im (t E₀ β η : ℝ) :
    (step1_zAt t E₀ β η).im = η / ouBandCoeff t := by
  unfold step1_zAt
  rw [Complex.mul_im, Complex.inv_re, Complex.inv_im, Complex.ofReal_re, Complex.ofReal_im]
  simp only [Complex.normSq_ofReal, neg_zero, zero_div, zero_mul, add_zero]
  field_simp

private theorem step1_zAt_pos_im (t E₀ β η : ℝ) (hη : 0 < η) : 0 < (step1_zAt t E₀ β η).im := by
  rw [step1_zAt_im]; exact div_pos hη (step1_ouBandCoeff_pos t)

/-- **Domain fitting**: for `t` small (bounded by `min κ 1/96*7`) and `1`, `|β| ≤ κ'/16`,
`0 < η ≤ 1/2`, `z(β,η) = a⁻¹(β+E₀+iη)` lies in the domain `|Re z| ≤ 2-κ/2`, `0 < Im z ≤ 1` of the
local law. -/
private theorem step1_zAt_domain {κ t E₀ β η : ℝ} (hκ0 : 0 < κ) (hκ2 : κ ≤ 2)
    (hE₀ : |E₀| ≤ 2 - κ) (hβ : |β| ≤ min κ 1 / 16) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (htκ : t ≤ 7 * κ / 96) (hη0 : 0 < η) (hη1 : η ≤ 1 / 2) :
    0 < (step1_zAt t E₀ β η).im ∧ (step1_zAt t E₀ β η).im ≤ 1 ∧
      |(step1_zAt t E₀ β η).re| ≤ 2 - κ / 2 := by
  have haInv := step1_ouBandCoeff_inv_le ht0 ht1
  have ha1 : (1:ℝ)/2 ≤ ouBandCoeff t := by
    have := step1_ouBandCoeff_ge (t := t)
    linarith
  refine ⟨step1_zAt_pos_im t E₀ β η hη0, ?_, ?_⟩
  · rw [step1_zAt_im, div_le_one (step1_ouBandCoeff_pos t)]
    linarith
  · rw [step1_zAt_re, abs_div, abs_of_pos (step1_ouBandCoeff_pos t)]
    rw [div_le_iff₀ (step1_ouBandCoeff_pos t)]
    have h1 := step1_re_z_bound hκ0 hκ2 hE₀ hβ ht0 htκ
    have haux : 1 ≤ (1 + 2 * t) * ouBandCoeff t := by
      have h2 := mul_le_mul_of_nonneg_left haInv (step1_ouBandCoeff_pos t).le
      rw [mul_inv_cancel₀ (step1_ouBandCoeff_pos t).ne'] at h2
      linarith
    nlinarith [abs_nonneg (β + E₀), mul_le_mul_of_nonneg_right h1 (step1_ouBandCoeff_pos t).le,
      mul_nonneg (abs_nonneg (β + E₀)) (sub_nonneg.mpr haux)]

/-- `g(N) = M(N)^{-1+step1Eps τs} < 1/2` always (`M(N) ≥ 3`, `0 < τs < 1`). -/
private theorem step1_g_lt_half (d : Dims) (N : ℕ) {τs : ℝ} (h0 : 0 < τs) (h1 : τs < 1) :
    (msize d N) ^ (-1 + step1Eps τs) < 1 / 2 := by
  have hL := d.three_le_L N
  have hW := d.W_pos N
  have hM3 : (3 : ℝ) ≤ msize d N := by
    unfold msize ouMatrixSize
    have : (3 : ℕ) ≤ d.L N * d.W N := by
      calc (3:ℕ) ≤ d.L N := hL
        _ ≤ d.L N * d.W N := Nat.le_mul_of_pos_right _ hW
    exact_mod_cast this
  have hexp : (-1 + step1Eps τs : ℝ) ≤ -3/4 := by unfold step1Eps; linarith
  calc (msize d N) ^ (-1 + step1Eps τs) ≤ (msize d N) ^ (-3/4 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) hexp
    _ ≤ (3 : ℝ) ^ (-3/4 : ℝ) := by
        apply Real.rpow_le_rpow_of_nonpos (by norm_num) hM3 (by norm_num)
    _ < 1 / 2 := by
        have h2lt3 : (2:ℝ) < (3:ℝ) ^ (3/4 : ℝ) := by
          have h1 : ((16:ℝ)) < ((27:ℝ)) := by norm_num
          have h2 : (16:ℝ) ^ ((1:ℝ)/4) < (27:ℝ) ^ ((1:ℝ)/4) :=
            Real.rpow_lt_rpow (by norm_num) h1 (by norm_num)
          have h3 : (16:ℝ) ^ ((1:ℝ)/4) = 2 := by
            rw [show (16:ℝ) = (2:ℝ) ^ (4:ℕ) by norm_num, ← Real.rpow_natCast (2:ℝ) 4,
              ← Real.rpow_mul (by norm_num)]
            norm_num
          have h4 : (27:ℝ) ^ ((1:ℝ)/4) = (3:ℝ) ^ (3/4 : ℝ) := by
            rw [show (27:ℝ) = (3:ℝ) ^ (3:ℕ) by norm_num, ← Real.rpow_natCast (3:ℝ) 3,
              ← Real.rpow_mul (by norm_num)]
            norm_num
          rw [h3, h4] at h2
          exact h2
        rw [show (-3/4 : ℝ) = -(3/4) by ring, Real.rpow_neg (by norm_num)]
        rw [inv_lt_iff_one_lt_mul₀ (by positivity : (0:ℝ) < (3:ℝ)^(3/4:ℝ))]
        nlinarith

/-- `N^{-1+τ} ≤ g(N) = M(N)^{-1+step1Eps τs}` eventually, for `τ ≤ step1Eps τs`. -/
private theorem step1_g_ge_Npow (d : Dims) {τs τ : ℝ} (h0 : 0 < τs) (h1 : τs < 1)
    (hτ : τ ≤ step1Eps τs) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-1 + τ) ≤ (msize d N) ^ (-1 + step1Eps τs) := by
  filter_upwards [d.dim, eventually_ge_atTop 1] with N hdim hN1
  have hM_le_N : msize d N ≤ (N : ℝ) := by
    unfold msize ouMatrixSize
    have h : d.L N * d.W N = d.W N * d.L N := by ring
    rw [h]; exact_mod_cast hdim.1
  have hMpos : (0 : ℝ) < msize d N := by
    have hL := d.three_le_L N; have hW := d.W_pos N
    unfold msize ouMatrixSize
    have : 0 < d.L N * d.W N := Nat.mul_pos (by omega) hW
    exact_mod_cast this
  have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have step1 : (N : ℝ) ^ (-1 + τ) ≤ (N : ℝ) ^ (-1 + step1Eps τs) :=
    Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
  have step2 : (N : ℝ) ^ (-1 + step1Eps τs) ≤ (msize d N) ^ (-1 + step1Eps τs) :=
    Real.rpow_le_rpow_of_nonpos hMpos hM_le_N (by unfold step1Eps; linarith)
  linarith

/-! ### `msize d N → ∞`, and eventual smallness of negative powers -/

private theorem step1_msize_pos (d : Dims) (N : ℕ) : 0 < msize d N := by
  have hL := d.three_le_L N
  have hW := d.W_pos N
  unfold msize ouMatrixSize
  have : 0 < d.L N * d.W N := Nat.mul_pos (by omega) hW
  exact_mod_cast this

private theorem step1_msize_eq_bandWL (d : Dims) (N : ℕ) :
    msize d N = ((Gauss.band d).W N : ℝ) * ((Gauss.band d).L N : ℝ) := by
  have hcardL : ((Gauss.band d).L N : ℝ) = (d.L N : ℝ) := by rw [band_L]
  have hcardW : ((Gauss.band d).W N : ℝ) = (d.W N : ℝ) := by rw [band_W]
  unfold msize ouMatrixSize
  rw [hcardL, hcardW]; push_cast; ring

private theorem step1_msize_eq_size (d : Dims) (N : ℕ) :
    msize d N = (((Gauss.band d).size N : ℕ) : ℝ) := by
  rw [step1_msize_eq_bandWL]
  unfold Band.size
  push_cast
  ring

private theorem step1_msize_tendsto_atTop (d : Dims) :
    Tendsto (fun N : ℕ => msize d N) atTop atTop := by
  have hsize : Tendsto (fun N : ℕ => (((Gauss.band d).size N : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (Gauss.band d).tendsto_size
  exact hsize.congr (fun N => (step1_msize_eq_size d N).symm)

/-- **Eventual smallness of a negative power of `msize`.** -/
private theorem step1_rpow_neg_eventually_le (d : Dims) {e c : ℝ} (he : e < 0) (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop, (msize d N) ^ e ≤ c := by
  have h1 : Tendsto (fun N : ℕ => msize d N) atTop atTop := step1_msize_tendsto_atTop d
  have hr := tendsto_rpow_neg_atTop (y := -e) (by linarith)
  have heq : (fun x : ℝ => x ^ (-(-e))) = (fun x : ℝ => x ^ e) := by
    funext x; congr 1; ring
  rw [heq] at hr
  have hcomp := hr.comp h1
  exact (hcomp.eventually (Iio_mem_nhds hc)).mono fun N h => h.le

/-! ### Elementary bounds on `ouZeta` -/

private theorem step1_ouBandCoeff_le_one {t : ℝ} (ht : 0 ≤ t) : ouBandCoeff t ≤ 1 := by
  unfold ouBandCoeff
  calc Real.exp (-t / 2) ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
    _ = 1 := Real.exp_zero

private theorem step1_ouZeta_def (t : ℝ) : ouZeta t = 1 - Real.exp (-t) := rfl

private theorem step1_ouZeta_le {t : ℝ} (ht0 : 0 ≤ t) : ouZeta t ≤ t := by
  have h := Real.add_one_le_exp (-t)
  rw [step1_ouZeta_def]; linarith

private theorem step1_ouZeta_pos {t : ℝ} (ht : 0 < t) : 0 < ouZeta t := by
  rw [step1_ouZeta_def]
  have : Real.exp (-t) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  linarith

/-- **`ζ(t) ≥ t/2`** for `0 ≤ t ≤ 1` (the `ζ ≍ t_*` direction). -/
private theorem step1_ouZeta_ge_half {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t / 2 ≤ ouZeta t := by
  have h1 : 1 + t ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
  have htpos : (0 : ℝ) < 1 + t := by linarith
  have h2 : Real.exp (-t) ≤ (1 + t)⁻¹ := by
    rw [Real.exp_neg]; exact inv_anti₀ htpos h1
  have h4 : (1 + t)⁻¹ ≤ 1 - t / 2 := by
    rw [inv_eq_one_div, div_le_iff₀ htpos]
    nlinarith
  rw [step1_ouZeta_def]
  linarith

/-! ### The combined local-law error, at a general threshold exponent `ρ` -/

private theorem step1_localErr_le (d : Dims) (N : ℕ) {z : ℂ} (hz : 0 < z.im) {τ' ρ : ℝ}
    (hτ'0 : 0 ≤ τ') (hτ'1 : τ' < 1)
    (hW : (msize d N) ^ (1 / 2 + d.c) ≤ ((Gauss.band d).W N : ℝ))
    (hη : (msize d N) ^ (-1 + ρ) ≤ z.im) :
    ((Gauss.band d).W N : ℝ) ^ τ' * ((Gauss.band d).zScale N z)⁻¹ ≤
      max ((msize d N) ^ ((1 / 2 + d.c) * (τ' - 1) + (1 - ρ) / 2)) ((msize d N) ^ (τ' - ρ)) := by
  have h1 := step1_error_le d N hz (τ' := τ')
  have h2 := step1_term1_le d N (τ' := τ') (ρ := ρ) hτ'1 hW hη
  have h3 := step1_term2_le d N (τ' := τ') (ρ := ρ) hτ'0 hη
  exact h1.trans (max_le_max h2 h3)

/-- **`msize d N ≥ 3` (always, not merely eventually).** -/
private theorem step1_msize_ge_three (d : Dims) (N : ℕ) : (3 : ℝ) ≤ msize d N := by
  have hL := d.three_le_L N
  have hW := d.W_pos N
  have h3 : (3 : ℕ) ≤ ouMatrixSize d N := by
    unfold ouMatrixSize
    calc (3 : ℕ) ≤ d.L N := hL
      _ ≤ d.L N * d.W N := Nat.le_mul_of_pos_right _ hW
  unfold msize
  exact_mod_cast h3

/-- **The `IsRegular51` local-law error, qualitative form**: eventually below any fixed positive
constant, uniformly at the grid scale `η ≥ g(N)` (`τ' = step1Prec τs`, `ρ = step1Eps τs`). -/
private theorem step1_localErr_reg_eventually (d : Dims) {τs : ℝ} (h0 : 0 < τs) (h1 : τs < 1)
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop, ∀ z : ℂ, 0 < z.im → (msize d N) ^ (-1 + step1Eps τs) ≤ z.im →
      ((Gauss.band d).W N : ℝ) ^ (step1Prec τs) * ((Gauss.band d).zScale N z)⁻¹ ≤ c := by
  have hτ'0 : (0 : ℝ) ≤ step1Prec τs := by unfold step1Prec; linarith
  have hτ'1 : step1Prec τs < 1 := by unfold step1Prec; linarith
  have hkey : d.c * (step1Prec τs - 1) < 0 := by
    have hpos : (0 : ℝ) < 1 - step1Prec τs := by unfold step1Prec; linarith
    nlinarith [mul_pos d.c_pos hpos]
  have he1 : (1 / 2 + d.c) * (step1Prec τs - 1) + (1 - step1Eps τs) / 2 < 0 := by
    unfold step1Prec step1Eps at *
    nlinarith [hkey]
  have he2 : step1Prec τs - step1Eps τs < 0 := by unfold step1Prec step1Eps; linarith
  filter_upwards [step1_W_ge_msize_rpow d,
    step1_rpow_neg_eventually_le d he1 hc, step1_rpow_neg_eventually_le d he2 hc]
    with N hW hc1 hc2
  intro z hz hη
  exact (step1_localErr_le d N hz hτ'0 hτ'1 hW hη).trans (max_le hc1 hc2)

/-! ### The `M^{-3}`-grid in `z`-space, and the grid-good high-probability event -/

/-- The grid point `z(β_p, η_q)`, `β_p` on `[-κ'/16,κ'/16]`, `η_q` on `[g(N), 1/2]`. -/
private noncomputable def step1_zGrid (d : Dims) (κ τs E₀ : ℝ) (N : ℕ)
    (k : Fin (step1_bC κ (msize d N) + 1) × Fin (step1_hC (msize d N) + 1)) : ℂ :=
  step1_zAt ((Gauss.band d).tPow τs N) E₀
    (step1_betaGrid κ (msize d N) k.1)
    (step1_etaGrid (msize d N) ((msize d N) ^ (-1 + step1Eps τs)) k.2)

/-- **The local law holds simultaneously at every grid point, with high probability.** -/
private theorem step1_gridGood_highProb (d : Dims) {κ : ℝ} (hκ0 : 0 < κ) (hκ2 : κ ≤ 2)
    (hLL : BandTracialLocalLaw d (κ / 2)) {τs E₀ : ℝ} (h0 : 0 < τs) (h1 : τs < 1)
    (hE₀ : |E₀| ≤ 2 - κ) :
    HighProb (P d) (fun N => ⋂ k : Fin (step1_bC κ (msize d N) + 1) ×
        Fin (step1_hC (msize d N) + 1),
      {ω | ‖RBM.stieltjes (Xmat d N ω) (step1_zGrid d κ τs E₀ N k) -
          msc (step1_zGrid d κ τs E₀ N k)‖ ≤
        ((Gauss.band d).W N : ℝ) ^ step1Prec τs *
          ((Gauss.band d).zScale N (step1_zGrid d κ τs E₀ N k))⁻¹}) := by
  have hτ0 : (0 : ℝ) < step1Eps τs := by unfold step1Eps; linarith
  have hτ1 : step1Eps τs < 1 := by unfold step1Eps; linarith
  have hτ'0 : (0 : ℝ) < step1Prec τs := by unfold step1Prec; linarith
  have hcard := step1_card_le d κ hκ0
  have hκ2' : κ / 2 ≤ 2 := by linarith
  refine HighProb.biInter (C := 8) (by norm_num) hcard ?_
  intro D hD
  have hunif := step1_uniform_of_hLL d hLL hκ2' hτ0 hτ1 hτ'0 hD
  filter_upwards [hunif, step1_tPow_eventually_le d h1 (show (0:ℝ) < 1 by norm_num),
    step1_tPow_eventually_le d h1 (show (0:ℝ) < 7 * κ / 96 by linarith),
    step1_g_ge_Npow d h0 h1 (le_refl (step1Eps τs))] with N hu ht1' htκ hgN
  intro k
  have hβmem : |step1_betaGrid κ (msize d N) k.1| ≤ min κ 1 / 16 :=
    step1_betaGrid_mem κ (msize d N) hκ0 k.1
  have hgpos : 0 < (msize d N) ^ (-1 + step1Eps τs) :=
    Real.rpow_pos_of_pos (step1_msize_pos d N) _
  have hηmem : (msize d N) ^ (-1 + step1Eps τs) ≤
        step1_etaGrid (msize d N) ((msize d N) ^ (-1 + step1Eps τs)) k.2 ∧
      step1_etaGrid (msize d N) ((msize d N) ^ (-1 + step1Eps τs)) k.2 ≤ 1 / 2 :=
    step1_etaGrid_mem (msize d N) ((msize d N) ^ (-1 + step1Eps τs))
      (step1_g_lt_half d N h0 h1).le k.2
  have hη0 : 0 < step1_etaGrid (msize d N) ((msize d N) ^ (-1 + step1Eps τs)) k.2 :=
    lt_of_lt_of_le hgpos hηmem.1
  obtain ⟨hzim0, hzim1, hzre⟩ := step1_zAt_domain hκ0 hκ2 hE₀ hβmem
    (step1_tPow_pos d τs N).le ht1' htκ hη0 hηmem.2
  have ha1 : ouBandCoeff ((Gauss.band d).tPow τs N) ≤ 1 :=
    step1_ouBandCoeff_le_one (step1_tPow_pos d τs N).le
  have hzimge : (N : ℝ) ^ (-1 + step1Eps τs) ≤ (step1_zGrid d κ τs E₀ N k).im := by
    show (N : ℝ) ^ (-1 + step1Eps τs) ≤ (step1_zAt ((Gauss.band d).tPow τs N) E₀
      (step1_betaGrid κ (msize d N) k.1)
      (step1_etaGrid (msize d N) ((msize d N) ^ (-1 + step1Eps τs)) k.2)).im
    rw [step1_zAt_im]
    have hstep : step1_etaGrid (msize d N) ((msize d N) ^ (-1 + step1Eps τs)) k.2 ≤
        step1_etaGrid (msize d N) ((msize d N) ^ (-1 + step1Eps τs)) k.2 /
          ouBandCoeff ((Gauss.band d).tPow τs N) := by
      rw [le_div_iff₀ (step1_ouBandCoeff_pos _)]
      nlinarith [hη0.le, ha1]
    calc (N : ℝ) ^ (-1 + step1Eps τs) ≤ (msize d N) ^ (-1 + step1Eps τs) := hgN
      _ ≤ step1_etaGrid (msize d N) ((msize d N) ^ (-1 + step1Eps τs)) k.2 := hηmem.1
      _ ≤ _ := hstep
  have hb := hu (step1_zGrid d κ τs E₀ N k) hzim0 hzim1 hzre hzimge
  have hset : ({ω | ‖RBM.stieltjes (Xmat d N ω) (step1_zGrid d κ τs E₀ N k) -
        msc (step1_zGrid d κ τs E₀ N k)‖ ≤
      ((Gauss.band d).W N : ℝ) ^ step1Prec τs *
        ((Gauss.band d).zScale N (step1_zGrid d κ τs E₀ N k))⁻¹})ᶜ =
      {ω | ((Gauss.band d).W N : ℝ) ^ step1Prec τs *
          ((Gauss.band d).zScale N (step1_zGrid d κ τs E₀ N k))⁻¹ <
        ‖RBM.stieltjes (Xmat d N ω) (step1_zGrid d κ τs E₀ N k) -
          msc (step1_zGrid d κ τs E₀ N k)‖} := by
    ext ω; simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le]
  rw [hset]
  exact hb

/-! ### Deterministic Lipschitz interpolation from the grid to the continuum -/

/-- `stieltjesVec` is Lipschitz with an explicit threshold on both imaginary parts. -/
private theorem step1_stieltjesVec_lip_threshold {n : Type*} [Fintype n] (v : n → ℝ) {z z' : ℂ}
    {θ : ℝ} (hθ : 0 < θ) (hz : θ ≤ z.im) (hz' : θ ≤ z'.im) :
    ‖stieltjesVec v z - stieltjesVec v z'‖ ≤ ‖z - z'‖ * θ⁻¹ ^ 2 := by
  have hz0 : 0 < z.im := lt_of_lt_of_le hθ hz
  have hz0' : 0 < z'.im := lt_of_lt_of_le hθ hz'
  have h1 := step1_stieltjesVec_lip v hz0 hz0'
  have hden : θ ^ 2 ≤ z.im * z'.im := by nlinarith
  rw [div_eq_mul_inv] at h1
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  rw [inv_pow]
  exact inv_anti₀ (by positivity) hden

/-- `msc` is Lipschitz on the bulk domain, with the bulk lower bound in place of `Im msc`. -/
private theorem step1_msc_lip_bulk {κ' : ℝ} (hκ0 : 0 < κ') (hκ1 : κ' ≤ 1) {z z' : ℂ}
    (hre : |z.re| ≤ 2 - κ' / 2) (hz0 : 0 < z.im) (hz1 : z.im ≤ 3) (hz'0 : 0 < z'.im) :
    ‖msc z' - msc z‖ ≤ ‖z' - z‖ * (12 / κ') := by
  have hb := step1_msc_im_ge hκ0 hκ1 hre hz0 hz1
  have hl := step1_msc_lip hz0 hz'0
  have h1 : ‖msc z' - msc z‖ * (κ' / 12) ≤ ‖msc z' - msc z‖ * (msc z).im :=
    mul_le_mul_of_nonneg_left hb (norm_nonneg _)
  have h2 : ‖msc z' - msc z‖ * (κ' / 12) ≤ ‖z' - z‖ := h1.trans hl
  have h3 : ‖msc z' - msc z‖ ≤ ‖z' - z‖ / (κ' / 12) := (le_div_iff₀ (by positivity)).mpr h2
  calc ‖msc z' - msc z‖ ≤ ‖z' - z‖ / (κ' / 12) := h3
    _ = ‖z' - z‖ * (12 / κ') := by field_simp

/-- **Deterministic interpolation**: the difference of the regularized errors at two nearby
spectral parameters `z(β,η)`, `z(βg,ηg)` (both in the bulk domain, both with imaginary part
`≥ θ > 0`, at horizontal distance `≤ s` in `(β,η)`-coordinates) is `≤ 6s(θ⁻² + 12/κ')`. -/
private theorem step1_interp_diff (d : Dims) (N : ℕ) (ω : Ω d)
    {t E₀ β η βg ηg κ : ℝ} (hκ0 : 0 < κ) (hκ2 : κ ≤ 2) (hE₀ : |E₀| ≤ 2 - κ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (htκ : t ≤ 7 * κ / 96)
    (hβ : |β| ≤ min κ 1 / 16) (hβg : |βg| ≤ min κ 1 / 16)
    {θ : ℝ} (hθ0 : 0 < θ) (hθη : θ ≤ η) (hθηg : θ ≤ ηg) (hη1 : η ≤ 1 / 2) (hηg1 : ηg ≤ 1 / 2)
    {s : ℝ} (hβsp : |β - βg| ≤ s) (hηsp : |η - ηg| ≤ s) :
    ‖(RBM.stieltjes (Xmat d N ω) (step1_zAt t E₀ β η) - msc (step1_zAt t E₀ β η)) -
        (RBM.stieltjes (Xmat d N ω) (step1_zAt t E₀ βg ηg) - msc (step1_zAt t E₀ βg ηg))‖ ≤
      6 * s * (θ⁻¹ ^ 2 + 12 / min κ 1) := by
  have hz0 : 0 < η := lt_of_lt_of_le hθ0 hθη
  have hzg0 : 0 < ηg := lt_of_lt_of_le hθ0 hθηg
  obtain ⟨hzim0, hzim1, hzre⟩ := step1_zAt_domain hκ0 hκ2 hE₀ hβ ht0 ht1 htκ hz0 hη1
  obtain ⟨hzgim0, hzgim1, hzgre⟩ := step1_zAt_domain hκ0 hκ2 hE₀ hβg ht0 ht1 htκ hzg0 hηg1
  have ha1 : ouBandCoeff t ≤ 1 := step1_ouBandCoeff_le_one ht0
  have hzθ : θ ≤ (step1_zAt t E₀ β η).im := by
    rw [step1_zAt_im]
    have : η ≤ η / ouBandCoeff t := by
      rw [le_div_iff₀ (step1_ouBandCoeff_pos t)]; nlinarith [hz0.le]
    linarith [hθη, this]
  have hzgθ : θ ≤ (step1_zAt t E₀ βg ηg).im := by
    rw [step1_zAt_im]
    have : ηg ≤ ηg / ouBandCoeff t := by
      rw [le_div_iff₀ (step1_ouBandCoeff_pos t)]; nlinarith [hzg0.le]
    linarith [hθηg, this]
  have hκ' : 0 < min κ 1 := lt_min hκ0 one_pos
  have hκ1' : min κ 1 ≤ 1 := min_le_right _ _
  have h1 : RBM.stieltjes (Xmat d N ω) (step1_zAt t E₀ β η) =
      stieltjesVec (Xmat_isHermitian d N ω).eigenvalues (step1_zAt t E₀ β η) :=
    step1_stieltjes_eq_stieltjesVec (Xmat_isHermitian d N ω) hzim0
  have h2 : RBM.stieltjes (Xmat d N ω) (step1_zAt t E₀ βg ηg) =
      stieltjesVec (Xmat_isHermitian d N ω).eigenvalues (step1_zAt t E₀ βg ηg) :=
    step1_stieltjes_eq_stieltjesVec (Xmat_isHermitian d N ω) hzgim0
  have hlipS := step1_stieltjesVec_lip_threshold (Xmat_isHermitian d N ω).eigenvalues hθ0 hzθ hzgθ
  have hzre' : |(step1_zAt t E₀ β η).re| ≤ 2 - min κ 1 / 2 := hzre.trans (by
    have := min_le_left κ (1 : ℝ); linarith)
  have hlipM := step1_msc_lip_bulk hκ' hκ1' hzre' hzim0
    (by linarith : (step1_zAt t E₀ β η).im ≤ 3) hzgim0
  have hzsub : step1_zAt t E₀ β η - step1_zAt t E₀ βg ηg =
      ((ouBandCoeff t : ℝ) : ℂ)⁻¹ * (⟨β - βg, η - ηg⟩ : ℂ) := by
    unfold step1_zAt
    rw [← mul_sub]
    congr 1
    apply Complex.ext <;> simp
  have hzdist : ‖step1_zAt t E₀ β η - step1_zAt t E₀ βg ηg‖ ≤ 6 * s := by
    rw [hzsub, norm_mul]
    have haB : ‖((ouBandCoeff t : ℝ) : ℂ)⁻¹‖ ≤ 3 := by
      rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (step1_ouBandCoeff_pos t).le]
      have := step1_ouBandCoeff_inv_le ht0 ht1
      linarith
    have hbB : ‖(⟨β - βg, η - ηg⟩ : ℂ)‖ ≤ 2 * s := by
      have h1 := Complex.norm_le_abs_re_add_abs_im (⟨β - βg, η - ηg⟩ : ℂ)
      simp only [Complex.add_re, Complex.add_im] at h1
      have h2 : |(⟨β - βg, η - ηg⟩ : ℂ).re| = |β - βg| := by simp
      have h3 : |(⟨β - βg, η - ηg⟩ : ℂ).im| = |η - ηg| := by simp
      rw [h2, h3] at h1
      linarith [hβsp, hηsp]
    calc ‖((ouBandCoeff t : ℝ) : ℂ)⁻¹‖ * ‖(⟨β - βg, η - ηg⟩ : ℂ)‖ ≤ 3 * (2 * s) :=
          mul_le_mul haB hbB (norm_nonneg _) (by norm_num)
      _ = 6 * s := by ring
  have htri : ‖(RBM.stieltjes (Xmat d N ω) (step1_zAt t E₀ β η) - msc (step1_zAt t E₀ β η)) -
        (RBM.stieltjes (Xmat d N ω) (step1_zAt t E₀ βg ηg) - msc (step1_zAt t E₀ βg ηg))‖ ≤
      ‖stieltjesVec (Xmat_isHermitian d N ω).eigenvalues (step1_zAt t E₀ β η) -
        stieltjesVec (Xmat_isHermitian d N ω).eigenvalues (step1_zAt t E₀ βg ηg)‖ +
      ‖msc (step1_zAt t E₀ βg ηg) - msc (step1_zAt t E₀ β η)‖ := by
    rw [h1, h2]
    have heq : (stieltjesVec (Xmat_isHermitian d N ω).eigenvalues (step1_zAt t E₀ β η) -
          msc (step1_zAt t E₀ β η)) -
        (stieltjesVec (Xmat_isHermitian d N ω).eigenvalues (step1_zAt t E₀ βg ηg) -
          msc (step1_zAt t E₀ βg ηg)) =
        (stieltjesVec (Xmat_isHermitian d N ω).eigenvalues (step1_zAt t E₀ β η) -
            stieltjesVec (Xmat_isHermitian d N ω).eigenvalues (step1_zAt t E₀ βg ηg)) +
          (msc (step1_zAt t E₀ βg ηg) - msc (step1_zAt t E₀ β η)) := by ring
    rw [heq]
    exact norm_add_le _ _
  refine htri.trans ?_
  rw [norm_sub_rev (step1_zAt t E₀ βg ηg) (step1_zAt t E₀ β η)] at hlipM
  calc ‖stieltjesVec (Xmat_isHermitian d N ω).eigenvalues (step1_zAt t E₀ β η) -
        stieltjesVec (Xmat_isHermitian d N ω).eigenvalues (step1_zAt t E₀ βg ηg)‖ +
      ‖msc (step1_zAt t E₀ βg ηg) - msc (step1_zAt t E₀ β η)‖ ≤
      ‖step1_zAt t E₀ β η - step1_zAt t E₀ βg ηg‖ * θ⁻¹ ^ 2 +
      ‖step1_zAt t E₀ β η - step1_zAt t E₀ βg ηg‖ * (12 / min κ 1) := add_le_add hlipS hlipM
    _ = ‖step1_zAt t E₀ β η - step1_zAt t E₀ βg ηg‖ * (θ⁻¹ ^ 2 + 12 / min κ 1) := by ring
    _ ≤ 6 * s * (θ⁻¹ ^ 2 + 12 / min κ 1) := by
        gcongr

/-! ### Miscellaneous eventual facts: `N^{1/2} ≪ N`, `Fintype.card (d.Idx N) = msize d N`,
the operator-norm high-probability event -/

private theorem step1_Nrpow_neg_eventually_le {e c : ℝ} (he : e < 0) (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ e ≤ c := by
  have h1 : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hr := tendsto_rpow_neg_atTop (y := -e) (by linarith)
  have heq : (fun x : ℝ => x ^ (-(-e))) = (fun x : ℝ => x ^ e) := by
    funext x; congr 1; ring
  rw [heq] at hr
  exact ((hr.comp h1).eventually (Iio_mem_nhds hc)).mono fun N h => h.le

/-- **`N^{1/2} + 2 ≤ N / 2` eventually.** -/
private theorem step1_sqrtN_eventually_le : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ ((1 : ℝ) / 2) + 2 ≤
    (N : ℝ) / 2 := by
  have h1 := step1_Nrpow_neg_eventually_le (e := -(1 / 2 : ℝ)) (by norm_num) (c := 1 / 4)
    (by norm_num)
  filter_upwards [h1, eventually_ge_atTop 8] with N hN hN8
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
  have hN8' : (8 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN8
  have heq : (N : ℝ) ^ ((1 : ℝ) / 2) = (N : ℝ) * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rcases eq_or_lt_of_le hN0 with h0 | h0
    · simp [← h0]
    · have e1 : (N : ℝ) ^ ((1 : ℝ) + (-(1 / 2 : ℝ))) =
          (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_add h0 1 (-(1 / 2))
      have e2 : (1 : ℝ) + (-(1 / 2 : ℝ)) = (1 : ℝ) / 2 := by norm_num
      rw [e2, Real.rpow_one] at e1
      exact e1
  rw [heq]
  have h2 : (N : ℝ) * (N : ℝ) ^ (-(1 / 2 : ℝ)) ≤ (N : ℝ) * (1 / 4) :=
    mul_le_mul_of_nonneg_left hN hN0
  linarith

/-- **`Fintype.card (d.Idx N) = msize d N`.** -/
private theorem step1_card_Idx_eq (d : Dims) (N : ℕ) :
    ((Fintype.card (d.Idx N) : ℕ) : ℝ) = msize d N := by
  unfold msize ouMatrixSize
  norm_cast
  simp [ZMod.card]

/-- **`msize d N ≥ N / 2` eventually** (from `RBM.Band.dim`, `N ≤ 2 W L`). -/
private theorem step1_msize_ge_half_eventually (d : Dims) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) / 2 ≤ msize d N := by
  filter_upwards [d.dim] with N hdim
  have h2 : (N : ℕ) ≤ 2 * (d.W N * d.L N) := hdim.2
  have hM : msize d N = (d.L N : ℝ) * (d.W N : ℝ) := by
    unfold msize ouMatrixSize; push_cast; ring
  have h2' : (N : ℝ) ≤ 2 * ((d.W N : ℝ) * (d.L N : ℝ)) := by exact_mod_cast h2
  rw [hM]; linarith

open scoped Matrix.Norms.L2Operator in
/-- **The operator-norm event**: `‖X‖ ≤ N^{1/2}` with high probability. -/
private theorem step1_opNorm_highProb (d : Dims) :
    HighProb (P d) (fun N => {ω | ‖Xmat d N ω‖ ≤ (N : ℝ) ^ ((1 : ℝ) / 2)}) := by
  have h := (stochDom_norm_Xmat_gauss d).highProb (τ := (1 / 2 : ℝ)) (by norm_num)
  have hset : ∀ N : ℕ, {ω : Ω d | ∀ _u : Unit, ‖Xmat d N ω‖ ≤ (N : ℝ) ^ ((1 : ℝ) / 2) * 1} =
      {ω : Ω d | ‖Xmat d N ω‖ ≤ (N : ℝ) ^ ((1 : ℝ) / 2)} := by
    intro N; ext ω; simp
  intro D hD
  filter_upwards [h D hD] with N hN
  rwa [hset] at hN

private theorem step1_msize_inv_eventually_le (d : Dims) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop, (msize d N)⁻¹ ≤ c :=
  ((tendsto_inv_atTop_zero.comp (step1_msize_tendsto_atTop d)).eventually
    (Iio_mem_nhds hc)).mono fun N h => h.le

/-- **The grid-interpolation slack is eventually below any fixed target `ε`**, at threshold
exponent `ρ ≥ 0` (used with `ρ = step1Eps τs` for regularity, `ρ = τs - τs/32` for the free
convolution). -/
private theorem step1_interp_slack_le (d : Dims) {κ ε ρ : ℝ} (hκ0 : 0 < κ) (hρ0 : 0 ≤ ρ)
    (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      6 * ((msize d N) ^ 3)⁻¹ * ((((msize d N) ^ (-1 + ρ))⁻¹) ^ 2 + 12 / min κ 1) ≤ ε := by
  set κ' := min κ 1 with hκ'_def
  have hκ'0 : 0 < κ' := lt_min hκ0 one_pos
  have hc : 0 < ε / (6 * (1 + 12 / κ')) := by positivity
  filter_upwards [step1_msize_inv_eventually_le d hc] with N hN
  have hM1 : (1 : ℝ) ≤ msize d N := by have := step1_msize_ge_three d N; linarith
  have hMpos := step1_msize_pos d N
  have hginvM : ((msize d N) ^ (-1 + ρ))⁻¹ ≤ msize d N := by
    have heq : ((msize d N) ^ (-1 + ρ))⁻¹ = (msize d N) ^ (1 - ρ) := by
      rw [show (1 - ρ : ℝ) = -(-1 + ρ) by ring, Real.rpow_neg hMpos.le]
    rw [heq]
    calc (msize d N) ^ (1 - ρ) ≤ (msize d N) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hM1 (by linarith)
      _ = msize d N := Real.rpow_one _
  have hb1 : (((msize d N) ^ (-1 + ρ))⁻¹) ^ 2 ≤ (msize d N) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hginvM 2
  have halg : ((msize d N) ^ 3)⁻¹ * (msize d N) ^ 2 = (msize d N)⁻¹ := by
    field_simp
  have hpiece1 : ((msize d N) ^ 3)⁻¹ * (((msize d N) ^ (-1 + ρ))⁻¹) ^ 2 ≤ (msize d N)⁻¹ := by
    calc ((msize d N) ^ 3)⁻¹ * (((msize d N) ^ (-1 + ρ))⁻¹) ^ 2 ≤
        ((msize d N) ^ 3)⁻¹ * (msize d N) ^ 2 :=
          mul_le_mul_of_nonneg_left hb1 (by positivity)
      _ = (msize d N)⁻¹ := halg
  have hM3geM : msize d N ≤ (msize d N) ^ 3 := by nlinarith [sq_nonneg (msize d N - 1), hM1]
  have hpiece2 : ((msize d N) ^ 3)⁻¹ * (12 / κ') ≤ (msize d N)⁻¹ * (12 / κ') :=
    mul_le_mul_of_nonneg_right (inv_anti₀ hMpos hM3geM) (by positivity)
  have htot : ((msize d N) ^ 3)⁻¹ * ((((msize d N) ^ (-1 + ρ))⁻¹) ^ 2 + 12 / κ') ≤
      (msize d N)⁻¹ * (1 + 12 / κ') := by
    have hdist : ((msize d N) ^ 3)⁻¹ * ((((msize d N) ^ (-1 + ρ))⁻¹) ^ 2 + 12 / κ') =
        ((msize d N) ^ 3)⁻¹ * (((msize d N) ^ (-1 + ρ))⁻¹) ^ 2 +
          ((msize d N) ^ 3)⁻¹ * (12 / κ') := by ring
    have hdist2 : (msize d N)⁻¹ * (1 + 12 / κ') =
        (msize d N)⁻¹ + (msize d N)⁻¹ * (12 / κ') := by ring
    rw [hdist, hdist2]
    exact add_le_add hpiece1 hpiece2
  have hnn : (0 : ℝ) ≤ 1 + 12 / κ' := by positivity
  calc 6 * ((msize d N) ^ 3)⁻¹ * ((((msize d N) ^ (-1 + ρ))⁻¹) ^ 2 + 12 / κ') =
      6 * (((msize d N) ^ 3)⁻¹ * ((((msize d N) ^ (-1 + ρ))⁻¹) ^ 2 + 12 / κ')) := by ring
    _ ≤ 6 * ((msize d N)⁻¹ * (1 + 12 / κ')) := by linarith [htot]
    _ ≤ 6 * (ε / (6 * (1 + 12 / κ')) * (1 + 12 / κ')) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hN hnn) (by norm_num)
    _ = ε := by field_simp

private theorem step1_ofReal_inv_mul_im (r : ℝ) (X : ℂ) :
    (((r : ℝ) : ℂ)⁻¹ * X).im = r⁻¹ * X.im := by
  rw [← Complex.ofReal_inv, Complex.im_ofReal_mul]

/-! ### The regularity conjunct of `IsRegular51`, deterministically on the grid-good and
operator-norm events -/

open scoped Matrix.Norms.L2Operator in
private theorem step1_reg_eventually (d : Dims) {κ : ℝ} (hκ0 : 0 < κ) (hκ2 : κ ≤ 2)
    (hLL : BandTracialLocalLaw d (κ / 2)) {τs E₀ : ℝ} (h0 : 0 < τs) (h1 : τs < 1)
    (hE₀ : |E₀| ≤ 2 - κ) :
    ∀ᶠ N : ℕ in atTop, ∀ ω : Ω d,
      (ω ∈ ⋂ k : Fin (step1_bC κ (msize d N) + 1) × Fin (step1_hC (msize d N) + 1),
        {ω | ‖RBM.stieltjes (Xmat d N ω) (step1_zGrid d κ τs E₀ N k) -
            msc (step1_zGrid d κ τs E₀ N k)‖ ≤
          ((Gauss.band d).W N : ℝ) ^ step1Prec τs *
            ((Gauss.band d).zScale N (step1_zGrid d κ τs E₀ N k))⁻¹}) →
      ‖Xmat d N ω‖ ≤ (N : ℝ) ^ ((1 : ℝ) / 2) →
      IsRegular51 (vOU d N τs E₀ ω) (msize d N ^ (-1 + step1Eps τs))
        (msize d N ^ (-step1Sig τs)) (cBulk κ) 2 1 := by
  have hκ'0 : 0 < min κ 1 := lt_min hκ0 one_pos
  have hκ'1 : min κ 1 ≤ 1 := min_le_right _ _
  have hSigPos : 0 < step1Sig τs := by unfold step1Sig; exact lt_min (by linarith) (by linarith)
  have hlocal := step1_localErr_reg_eventually d h0 h1 (c := min κ 1 / 48) (by positivity)
  have hinterp := step1_interp_slack_le d (κ := κ) (ε := min κ 1 / 48) (ρ := step1Eps τs) hκ0
    (by unfold step1Eps; linarith) (by positivity)
  have hG_le := step1_rpow_neg_eventually_le d (e := -step1Sig τs) (by linarith)
    (c := min κ 1 / 16) (by positivity)
  have htb1 := step1_tPow_eventually_le d h1 (show (0 : ℝ) < 1 by norm_num)
  have htb2 := step1_tPow_eventually_le d h1 (show (0 : ℝ) < 7 * κ / 96 by linarith)
  have htb3 := step1_tPow_eventually_le d h1 (show (0 : ℝ) < 1 / 5 by norm_num)
  filter_upwards [hlocal, hinterp, hG_le, htb1, htb2, htb3, step1_sqrtN_eventually_le,
    step1_msize_ge_half_eventually d] with N hlocal' hinterp' hGle htb1' htb2' htb3' hsqrtN
    hmsizehalf
  intro ω hgood hnorm
  have hMpos := step1_msize_pos d N
  have hM1 : (1 : ℝ) ≤ msize d N := by have := step1_msize_ge_three d N; linarith
  set t := (Gauss.band d).tPow τs N with ht_def
  set a := ouBandCoeff t with ha_def
  have ht0 : 0 ≤ t := (step1_tPow_pos d τs N).le
  have ha_pos := step1_ouBandCoeff_pos t
  have ha_le1 : a ≤ 1 := step1_ouBandCoeff_le_one ht0
  have ha_inv_le : a⁻¹ ≤ 1 + 2 * t := step1_ouBandCoeff_inv_le ht0 htb1'
  have ha_inv_ge1 : 1 ≤ a⁻¹ := by
    rw [le_inv_comm₀ one_pos ha_pos, inv_one]; exact ha_le1
  have hgpos : 0 < (msize d N) ^ (-1 + step1Eps τs) := Real.rpow_pos_of_pos hMpos _
  -- **The bulk claim**, uniformly over the grid-covered window.
  have hBulk : ∀ β η' : ℝ, |β| ≤ min κ 1 / 16 → (msize d N) ^ (-1 + step1Eps τs) ≤ η' →
      η' ≤ 1 / 2 →
      min κ 1 / 24 ≤ (stieltjesVec (vOU d N τs E₀ ω) (⟨β, η'⟩ : ℂ)).im ∧
      (stieltjesVec (vOU d N τs E₀ ω) (⟨β, η'⟩ : ℂ)).im ≤ 2 := by
    intro β η' hβmem hη'0 hη'1
    obtain ⟨hβl, hβr⟩ := abs_le.mp hβmem
    obtain ⟨p, hp⟩ := step1_grid_exists (a := -(min κ 1 / 16)) (b := min κ 1 / 16)
      (by linarith) (step1_bC_pos κ (msize d N)) hβl hβr
    obtain ⟨q, hq⟩ := step1_grid_exists (a := (msize d N) ^ (-1 + step1Eps τs)) (b := (1 : ℝ) / 2)
      (step1_g_lt_half d N h0 h1) (step1_hC_pos (msize d N)) hη'0 hη'1
    have hbeq : min κ 1 / 16 - -(min κ 1 / 16) = min κ 1 / 8 := by ring
    rw [hbeq] at hp
    have hβsp : |β - step1_betaGrid κ (msize d N) p| ≤ (msize d N ^ 3)⁻¹ :=
      hp.trans (step1_betaGrid_spacing κ (msize d N) hκ0 hMpos)
    have hηsp : |η' - step1_etaGrid (msize d N) ((msize d N) ^ (-1 + step1Eps τs)) q| ≤
        (msize d N ^ 3)⁻¹ :=
      hq.trans (step1_etaGrid_spacing (msize d N) ((msize d N) ^ (-1 + step1Eps τs)) hMpos
        hgpos.le (step1_g_lt_half d N h0 h1).le)
    set βg := step1_betaGrid κ (msize d N) p with hβg_def
    set ηg := step1_etaGrid (msize d N) ((msize d N) ^ (-1 + step1Eps τs)) q with hηg_def
    have hβgmem : |βg| ≤ min κ 1 / 16 := step1_betaGrid_mem κ (msize d N) hκ0 p
    have hηgmem : (msize d N) ^ (-1 + step1Eps τs) ≤ ηg ∧ ηg ≤ 1 / 2 :=
      step1_etaGrid_mem (msize d N) ((msize d N) ^ (-1 + step1Eps τs))
        (step1_g_lt_half d N h0 h1).le q
    have hzgim_pos : 0 < ηg := lt_of_lt_of_le hgpos hηgmem.1
    have hgg : ‖RBM.stieltjes (Xmat d N ω) (step1_zGrid d κ τs E₀ N (p, q)) -
          msc (step1_zGrid d κ τs E₀ N (p, q))‖ ≤
        ((Gauss.band d).W N : ℝ) ^ step1Prec τs *
          ((Gauss.band d).zScale N (step1_zGrid d κ τs E₀ N (p, q)))⁻¹ :=
      Set.mem_iInter.mp hgood (p, q)
    have hzgim_ge : (msize d N) ^ (-1 + step1Eps τs) ≤ (step1_zAt t E₀ βg ηg).im := by
      rw [step1_zAt_im]
      have : ηg ≤ ηg / a := by
        rw [le_div_iff₀ ha_pos]; nlinarith [hzgim_pos.le, ha_le1]
      linarith [hηgmem.1, this]
    have hzgim_pos' : 0 < (step1_zAt t E₀ βg ηg).im := by
      rw [step1_zAt_im]; exact div_pos hzgim_pos ha_pos
    have hlocalbound := hlocal' (step1_zAt t E₀ βg ηg) hzgim_pos' hzgim_ge
    have hggbound : ‖RBM.stieltjes (Xmat d N ω) (step1_zAt t E₀ βg ηg) -
        msc (step1_zAt t E₀ βg ηg)‖ ≤ min κ 1 / 48 := hgg.trans hlocalbound
    have hdiffbound := step1_interp_diff d N ω (t := t) (E₀ := E₀) (β := β) (η := η')
      (βg := βg) (ηg := ηg) (κ := κ) hκ0 hκ2 hE₀ ht0 htb1' htb2' hβmem hβgmem
      (θ := (msize d N) ^ (-1 + step1Eps τs)) hgpos hη'0 hηgmem.1 hη'1 hηgmem.2 hβsp hηsp
    have hfinalbound : ‖RBM.stieltjes (Xmat d N ω) (step1_zAt t E₀ β η') -
        msc (step1_zAt t E₀ β η')‖ ≤ min κ 1 / 24 := by
      have heq : RBM.stieltjes (Xmat d N ω) (step1_zAt t E₀ β η') -
            msc (step1_zAt t E₀ β η') =
          ((RBM.stieltjes (Xmat d N ω) (step1_zAt t E₀ β η') - msc (step1_zAt t E₀ β η')) -
              (RBM.stieltjes (Xmat d N ω) (step1_zAt t E₀ βg ηg) -
                msc (step1_zAt t E₀ βg ηg))) +
            (RBM.stieltjes (Xmat d N ω) (step1_zAt t E₀ βg ηg) - msc (step1_zAt t E₀ βg ηg)) := by
        ring
      rw [heq]
      calc ‖(RBM.stieltjes (Xmat d N ω) (step1_zAt t E₀ β η') - msc (step1_zAt t E₀ β η')) -
            (RBM.stieltjes (Xmat d N ω) (step1_zAt t E₀ βg ηg) -
              msc (step1_zAt t E₀ βg ηg)) +
          (RBM.stieltjes (Xmat d N ω) (step1_zAt t E₀ βg ηg) - msc (step1_zAt t E₀ βg ηg))‖ ≤
          ‖(RBM.stieltjes (Xmat d N ω) (step1_zAt t E₀ β η') - msc (step1_zAt t E₀ β η')) -
              (RBM.stieltjes (Xmat d N ω) (step1_zAt t E₀ βg ηg) -
                msc (step1_zAt t E₀ βg ηg))‖ +
            ‖RBM.stieltjes (Xmat d N ω) (step1_zAt t E₀ βg ηg) -
              msc (step1_zAt t E₀ βg ηg)‖ := norm_add_le _ _
        _ ≤ min κ 1 / 48 + min κ 1 / 48 := add_le_add (hdiffbound.trans hinterp') hggbound
        _ = min κ 1 / 24 := by ring
    have hη'0' : 0 < η' := lt_of_lt_of_le hgpos hη'0
    obtain ⟨hzim0, hzim1, hzre⟩ := step1_zAt_domain hκ0 hκ2 hE₀ hβmem ht0 htb1' htb2' hη'0' hη'1
    have hzre' : |(step1_zAt t E₀ β η').re| ≤ 2 - min κ 1 / 2 := hzre.trans (by
      have := min_le_left κ (1 : ℝ); linarith)
    have hmscim := step1_msc_im_ge hκ'0 hκ'1 hzre' hzim0
      (by linarith : (step1_zAt t E₀ β η').im ≤ 3)
    have hmscnorm := norm_msc_lt_one (z := step1_zAt t E₀ β η') hzim0
    have hIm1 : |(RBM.stieltjes (Xmat d N ω) (step1_zAt t E₀ β η')).im -
        (msc (step1_zAt t E₀ β η')).im| ≤ min κ 1 / 24 := by
      calc |(RBM.stieltjes (Xmat d N ω) (step1_zAt t E₀ β η')).im -
            (msc (step1_zAt t E₀ β η')).im| =
          |(RBM.stieltjes (Xmat d N ω) (step1_zAt t E₀ β η') -
            msc (step1_zAt t E₀ β η')).im| := by rw [Complex.sub_im]
        _ ≤ ‖RBM.stieltjes (Xmat d N ω) (step1_zAt t E₀ β η') - msc (step1_zAt t E₀ β η')‖ :=
            Complex.abs_im_le_norm _
        _ ≤ min κ 1 / 24 := hfinalbound
    have hStIm_lb : min κ 1 / 24 ≤
        (RBM.stieltjes (Xmat d N ω) (step1_zAt t E₀ β η')).im := by
      have h1 := (abs_le.mp hIm1).1
      linarith [hmscim]
    have hStIm_ub : (RBM.stieltjes (Xmat d N ω) (step1_zAt t E₀ β η')).im ≤
        1 + min κ 1 / 24 := by
      have h1 := (abs_le.mp hIm1).2
      have h2 : (msc (step1_zAt t E₀ β η')).im < 1 :=
        lt_of_le_of_lt ((le_abs_self _).trans ((Complex.abs_im_le_norm _).trans le_rfl))
          hmscnorm
      linarith
    have heqvec : stieltjesVec (vOU d N τs E₀ ω) (⟨β, η'⟩ : ℂ) =
        ((a : ℝ) : ℂ)⁻¹ * RBM.stieltjes (Xmat d N ω) (step1_zAt t E₀ β η') := by
      have hw := step1_vOU_stieltjesVec_eq d N τs E₀ ω (w := (⟨β, η'⟩ : ℂ)) hη'0'
      have hargeq : ((a : ℝ) : ℂ)⁻¹ * ((⟨β, η'⟩ : ℂ) + (E₀ : ℂ)) = step1_zAt t E₀ β η' := by
        have hri : ((⟨β, η'⟩ : ℂ) + (E₀ : ℂ)) = (⟨β + E₀, η'⟩ : ℂ) := by
          apply Complex.ext <;> simp
        unfold step1_zAt
        rw [hri]
      rw [hw, hargeq]
    have heqIm : (stieltjesVec (vOU d N τs E₀ ω) (⟨β, η'⟩ : ℂ)).im =
        a⁻¹ * (RBM.stieltjes (Xmat d N ω) (step1_zAt t E₀ β η')).im := by
      rw [heqvec, step1_ofReal_inv_mul_im]
    rw [heqIm]
    have hXnonneg : 0 ≤ (RBM.stieltjes (Xmat d N ω) (step1_zAt t E₀ β η')).im := by
      linarith only [hStIm_lb, hκ'0]
    refine ⟨?_, ?_⟩
    · calc min κ 1 / 24 ≤ (RBM.stieltjes (Xmat d N ω) (step1_zAt t E₀ β η')).im := hStIm_lb
        _ = 1 * (RBM.stieltjes (Xmat d N ω) (step1_zAt t E₀ β η')).im := (one_mul _).symm
        _ ≤ a⁻¹ * (RBM.stieltjes (Xmat d N ω) (step1_zAt t E₀ β η')).im :=
            mul_le_mul_of_nonneg_right ha_inv_ge1 hXnonneg
    · have h1 : a⁻¹ * (RBM.stieltjes (Xmat d N ω) (step1_zAt t E₀ β η')).im ≤
          (1 + 2 * t) * (1 + min κ 1 / 24) :=
        mul_le_mul ha_inv_le hStIm_ub hXnonneg (by linarith only [ht0])
      have h2 : (1 + 2 * t) * (1 + min κ 1 / 24) ≤ 2 := by
        nlinarith only [htb3', hκ'1, hκ'0]
      linarith only [h1, h2]
  have hcBulk24 : cBulk κ ≤ min κ 1 / 24 := by unfold cBulk; nlinarith [hκ'0]
  constructor
  · intro E η hEmem hηg hη10
    have hEmem' : |E| ≤ min κ 1 / 16 := hEmem.trans hGle
    by_cases hη12 : η ≤ (1 / 2 : ℝ)
    · obtain ⟨hb1, hb2⟩ := hBulk E η hEmem' hηg hη12
      exact ⟨hcBulk24.trans hb1, hb2⟩
    · have hη12' : (1 : ℝ) / 2 < η := not_le.mp hη12
      have hlb := hBulk E (1 / 2) hEmem' (step1_g_lt_half d N h0 h1).le le_rfl
      have hmono := step1_stieltjesVec_im_mono (vOU d N τs E₀ ω) E
        (η₁ := 1 / 2) (η₂ := η) (by norm_num) hη12'.le
      have hub : (stieltjesVec (vOU d N τs E₀ ω) (⟨E, η⟩ : ℂ)).im ≤ 2 := by
        have hnb := step1_stieltjesVec_norm_le (vOU d N τs E₀ ω) (z := (⟨E, η⟩ : ℂ))
          (show (0 : ℝ) < (⟨E, η⟩ : ℂ).im by
            show (0 : ℝ) < η; linarith)
        have h2 : (⟨E, η⟩ : ℂ).im⁻¹ ≤ 2 := by
          have heq : (⟨E, η⟩ : ℂ).im = η := rfl
          rw [heq]
          rw [inv_le_comm₀ (by linarith) (by norm_num)]
          linarith
        calc (stieltjesVec (vOU d N τs E₀ ω) (⟨E, η⟩ : ℂ)).im ≤
            ‖stieltjesVec (vOU d N τs E₀ ω) (⟨E, η⟩ : ℂ)‖ :=
              (le_abs_self _).trans (Complex.abs_im_le_norm _)
          _ ≤ (⟨E, η⟩ : ℂ).im⁻¹ := hnb
          _ ≤ 2 := h2
      refine ⟨?_, hub⟩
      have hlow : (1 / 2 : ℝ) * (min κ 1 / 24) ≤
          η * (stieltjesVec (vOU d N τs E₀ ω) (⟨E, η⟩ : ℂ)).im := by
        refine le_trans ?_ hmono
        exact mul_le_mul_of_nonneg_left hlb.1 (by norm_num)
      have hηpos : 0 < η := by linarith
      have hlow' : (1 / 2 * (min κ 1 / 24)) / η ≤
          (stieltjesVec (vOU d N τs E₀ ω) (⟨E, η⟩ : ℂ)).im := by
        rw [div_le_iff₀ hηpos]
        calc (1 / 2 : ℝ) * (min κ 1 / 24) ≤
            η * (stieltjesVec (vOU d N τs E₀ ω) (⟨E, η⟩ : ℂ)).im := hlow
          _ = (stieltjesVec (vOU d N τs E₀ ω) (⟨E, η⟩ : ℂ)).im * η := by ring
      have hcBulk : cBulk κ ≤ min κ 1 / 480 := by unfold cBulk; nlinarith [hκ'0]
      refine le_trans hcBulk ?_
      have hstep : min κ 1 / 480 ≤ (1 / 2 * (min κ 1 / 24)) / η := by
        rw [le_div_iff₀ hηpos]
        nlinarith [mul_le_mul_of_nonneg_left hη10 (show (0:ℝ) ≤ min κ 1 / 480 by positivity)]
      exact hstep.trans hlow'
  · intro i
    rw [Real.rpow_one, step1_card_Idx_eq]
    unfold vOU
    have heig : |(Xmat_isHermitian d N ω).eigenvalues i| ≤ ‖Xmat d N ω‖ :=
      step1_eigenvalue_abs_le_norm (Xmat_isHermitian d N ω) i
    have h1 : |a * (Xmat_isHermitian d N ω).eigenvalues i - E₀| ≤
        |a * (Xmat_isHermitian d N ω).eigenvalues i| + |E₀| := by
      have hh := abs_add_le (a * (Xmat_isHermitian d N ω).eigenvalues i) (-E₀)
      simpa [sub_eq_add_neg] using hh
    have h2a : a * |(Xmat_isHermitian d N ω).eigenvalues i| ≤ (N : ℝ) ^ ((1 : ℝ) / 2) := by
      calc a * |(Xmat_isHermitian d N ω).eigenvalues i| ≤ 1 * ‖Xmat d N ω‖ :=
            mul_le_mul ha_le1 heig (abs_nonneg _) zero_le_one
        _ = ‖Xmat d N ω‖ := one_mul _
        _ ≤ (N : ℝ) ^ ((1 : ℝ) / 2) := hnorm
    have h2 : |a * (Xmat_isHermitian d N ω).eigenvalues i| =
        a * |(Xmat_isHermitian d N ω).eigenvalues i| := by
      rw [abs_mul, abs_of_pos ha_pos]
    rw [h2] at h1
    linarith [h1, h2a, hsqrtN, hmsizehalf, abs_nonneg E₀, hE₀]

/-! ### The free-convolution conjunct, via `freeConv_stable_local` -/

/-- **Sharpened local-law rate** at `Im z ≥ C M^{-1+τ_*}`: `W^{τ'}/zScale ≤ M^{-25τ_*/64}`
(`= M^{-step1Rate τs} · M^{-τ_*/64}`; the extra `M^{-τ_*/64}` absorbs fixed constants). -/
private theorem step1_localErr_fc_sharp (d : Dims) {τs : ℝ} (h0 : 0 < τs) (h1 : τs < 1)
    {C : ℝ} (hC : 0 < C) :
    ∀ᶠ N : ℕ in atTop, ∀ z : ℂ, 0 < z.im → C * (msize d N) ^ (-1 + τs) ≤ z.im →
      ((Gauss.band d).W N : ℝ) ^ (step1Prec τs) * ((Gauss.band d).zScale N z)⁻¹ ≤
        (msize d N) ^ (-(25 * τs / 64)) := by
  have hτ'0 : (0 : ℝ) ≤ step1Prec τs := by unfold step1Prec; linarith
  have hτ'1 : step1Prec τs < 1 := by unfold step1Prec; linarith
  set ρ2 : ℝ := τs - τs / 32 with hρ2_def
  have hkey : d.c * (step1Prec τs - 1) < 0 := by
    have hpos : (0 : ℝ) < 1 - step1Prec τs := by unfold step1Prec; linarith
    nlinarith [mul_pos d.c_pos hpos]
  have hexp1 : (1 / 2 + d.c) * (step1Prec τs - 1) + (1 - ρ2) / 2 ≤ -(25 * τs / 64) := by
    unfold step1Prec at *
    rw [hρ2_def]
    nlinarith [hkey]
  have hexp2 : step1Prec τs - ρ2 ≤ -(25 * τs / 64) := by
    unfold step1Prec; rw [hρ2_def]; linarith
  filter_upwards [step1_W_ge_msize_rpow d,
    step1_rpow_neg_eventually_le d (show (-(τs / 32) : ℝ) < 0 by linarith) hC]
    with N hW hCa
  intro z hz hη
  have hM0 : 0 < msize d N := step1_msize_pos d N
  have hM1 : (1 : ℝ) ≤ msize d N := by have := step1_msize_ge_three d N; linarith
  have hη' : (msize d N) ^ (-1 + ρ2) ≤ z.im := by
    have heq : (msize d N) ^ (-1 + ρ2) =
        (msize d N) ^ (-(τs / 32)) * (msize d N) ^ (-1 + τs) := by
      rw [show (-1 + ρ2 : ℝ) = -(τs / 32) + (-1 + τs) by rw [hρ2_def]; ring]
      exact Real.rpow_add hM0 _ _
    rw [heq]
    calc (msize d N) ^ (-(τs / 32)) * (msize d N) ^ (-1 + τs) ≤
        C * (msize d N) ^ (-1 + τs) :=
          mul_le_mul_of_nonneg_right hCa (Real.rpow_nonneg hM0.le _)
      _ ≤ z.im := hη
  have hb := step1_localErr_le d N hz hτ'0 hτ'1 hW hη'
  refine hb.trans (max_le ?_ ?_)
  · exact Real.rpow_le_rpow_of_exponent_le hM1 hexp1
  · exact Real.rpow_le_rpow_of_exponent_le hM1 hexp2

/-- **Deterministic size of the interpolation slack**: `≤ 6 (1 + 12/κ') M^{-1}` for `ρ ≥ 0`. -/
private theorem step1_interp_slack_det (d : Dims) (N : ℕ) {κ ρ : ℝ} (hκ0 : 0 < κ)
    (hρ0 : 0 ≤ ρ) :
    6 * ((msize d N) ^ 3)⁻¹ * ((((msize d N) ^ (-1 + ρ))⁻¹) ^ 2 + 12 / min κ 1) ≤
      6 * (1 + 12 / min κ 1) * (msize d N)⁻¹ := by
  set κ' := min κ 1 with hκ'_def
  have hκ'0 : 0 < κ' := lt_min hκ0 one_pos
  have hM1 : (1 : ℝ) ≤ msize d N := by have := step1_msize_ge_three d N; linarith
  have hMpos := step1_msize_pos d N
  have hginvM : ((msize d N) ^ (-1 + ρ))⁻¹ ≤ msize d N := by
    have heq : ((msize d N) ^ (-1 + ρ))⁻¹ = (msize d N) ^ (1 - ρ) := by
      rw [show (1 - ρ : ℝ) = -(-1 + ρ) by ring, Real.rpow_neg hMpos.le]
    rw [heq]
    calc (msize d N) ^ (1 - ρ) ≤ (msize d N) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hM1 (by linarith)
      _ = msize d N := Real.rpow_one _
  have hb1 : (((msize d N) ^ (-1 + ρ))⁻¹) ^ 2 ≤ (msize d N) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hginvM 2
  have halg : ((msize d N) ^ 3)⁻¹ * (msize d N) ^ 2 = (msize d N)⁻¹ := by
    field_simp
  have hpiece1 : ((msize d N) ^ 3)⁻¹ * (((msize d N) ^ (-1 + ρ))⁻¹) ^ 2 ≤ (msize d N)⁻¹ := by
    calc ((msize d N) ^ 3)⁻¹ * (((msize d N) ^ (-1 + ρ))⁻¹) ^ 2 ≤
        ((msize d N) ^ 3)⁻¹ * (msize d N) ^ 2 :=
          mul_le_mul_of_nonneg_left hb1 (by positivity)
      _ = (msize d N)⁻¹ := halg
  have hM3geM : msize d N ≤ (msize d N) ^ 3 := by nlinarith [sq_nonneg (msize d N - 1), hM1]
  have hpiece2 : ((msize d N) ^ 3)⁻¹ * (12 / κ') ≤ (msize d N)⁻¹ * (12 / κ') :=
    mul_le_mul_of_nonneg_right (inv_anti₀ hMpos hM3geM) (by positivity)
  have htot : ((msize d N) ^ 3)⁻¹ * ((((msize d N) ^ (-1 + ρ))⁻¹) ^ 2 + 12 / κ') ≤
      (msize d N)⁻¹ * (1 + 12 / κ') := by
    have hdist : ((msize d N) ^ 3)⁻¹ * ((((msize d N) ^ (-1 + ρ))⁻¹) ^ 2 + 12 / κ') =
        ((msize d N) ^ 3)⁻¹ * (((msize d N) ^ (-1 + ρ))⁻¹) ^ 2 +
          ((msize d N) ^ 3)⁻¹ * (12 / κ') := by ring
    have hdist2 : (msize d N)⁻¹ * (1 + 12 / κ') =
        (msize d N)⁻¹ + (msize d N)⁻¹ * (12 / κ') := by ring
    rw [hdist, hdist2]
    exact add_le_add hpiece1 hpiece2
  nlinarith [htot]

/-- **The interpolation slack is eventually below `M^{-25τ_*/64}`.** -/
private theorem step1_interp_slack_rate (d : Dims) {κ ρ τs : ℝ} (hκ0 : 0 < κ) (hρ0 : 0 ≤ ρ)
    (h1 : τs < 1) :
    ∀ᶠ N : ℕ in atTop,
      6 * ((msize d N) ^ 3)⁻¹ * ((((msize d N) ^ (-1 + ρ))⁻¹) ^ 2 + 12 / min κ 1) ≤
        (msize d N) ^ (-(25 * τs / 64)) := by
  have hκ'0 : 0 < min κ 1 := lt_min hκ0 one_pos
  have hK : 0 < 6 * (1 + 12 / min κ 1) := by positivity
  filter_upwards [step1_rpow_neg_eventually_le d (e := -1 + 25 * τs / 64) (by linarith)
    (c := (6 * (1 + 12 / min κ 1))⁻¹) (inv_pos.mpr hK)] with N hN
  have hMpos := step1_msize_pos d N
  refine (step1_interp_slack_det d N hκ0 hρ0).trans ?_
  have hsplit : (msize d N)⁻¹ =
      (msize d N) ^ (-1 + 25 * τs / 64) * (msize d N) ^ (-(25 * τs / 64)) := by
    rw [← Real.rpow_add hMpos, show (-1 + 25 * τs / 64 + -(25 * τs / 64) : ℝ) = -1 by ring,
      Real.rpow_neg_one]
  rw [hsplit, ← mul_assoc]
  have hq : 0 ≤ (msize d N) ^ (-(25 * τs / 64)) := Real.rpow_nonneg hMpos.le _
  have h2 : 6 * (1 + 12 / min κ 1) * (msize d N) ^ (-1 + 25 * τs / 64) ≤ 1 := by
    calc 6 * (1 + 12 / min κ 1) * (msize d N) ^ (-1 + 25 * τs / 64) ≤
        6 * (1 + 12 / min κ 1) * (6 * (1 + 12 / min κ 1))⁻¹ :=
          mul_le_mul_of_nonneg_left hN hK.le
      _ = 1 := mul_inv_cancel₀ hK.ne'
  calc 6 * (1 + 12 / min κ 1) * (msize d N) ^ (-1 + 25 * τs / 64) *
        (msize d N) ^ (-(25 * τs / 64)) ≤ 1 * (msize d N) ^ (-(25 * τs / 64)) :=
        mul_le_mul_of_nonneg_right h2 hq
    _ = (msize d N) ^ (-(25 * τs / 64)) := one_mul _

/-- `(M^3)⁻¹ = M^{-2-τ_*} · M^{-1+τ_*}`. -/
private theorem step1_inv_cube_eq (d : Dims) (N : ℕ) (τs : ℝ) :
    ((msize d N) ^ 3)⁻¹ = (msize d N) ^ (-2 - τs) * (msize d N) ^ (-1 + τs) := by
  have hMpos := step1_msize_pos d N
  rw [← Real.rpow_add hMpos, show (-2 - τs + (-1 + τs) : ℝ) = -((3 : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_neg hMpos.le, Real.rpow_natCast]

/-- `tPow τs N = M^{-1+τ_*}`. -/
private theorem step1_tPow_eq (d : Dims) (τs : ℝ) (N : ℕ) :
    (Gauss.band d).tPow τs N = (msize d N) ^ (-1 + τs) := by
  unfold Band.tPow; rw [step1_msize_eq_size]

/-- **The free-convolution conjunct on the grid-good event**: for the constants
`c₀, C₀` of `FreeConvStability.freeConv_stable_local`, eventually in `N`, every `ω` in the
grid-good event has `ρ_fc,ζ(t_*)(0)` existing and `M^{-3τ_*/8}`-close to `ρ_sc(E₀)`. -/
private theorem step1_fc_eventually (d : Dims) {κ : ℝ} (hκ0 : 0 < κ) (hκ2 : κ ≤ 2)
    {τs E₀ : ℝ} (h0 : 0 < τs) (h1 : τs < 1) (hE₀ : |E₀| ≤ 2 - κ) :
    ∀ᶠ N : ℕ in atTop, ∀ ω : Ω d,
      (ω ∈ ⋂ k : Fin (step1_bC κ (msize d N) + 1) × Fin (step1_hC (msize d N) + 1),
        {ω | ‖RBM.stieltjes (Xmat d N ω) (step1_zGrid d κ τs E₀ N k) -
            msc (step1_zGrid d κ τs E₀ N k)‖ ≤
          ((Gauss.band d).W N : ℝ) ^ step1Prec τs *
            ((Gauss.band d).zScale N (step1_zGrid d κ τs E₀ N k))⁻¹}) →
      ∃ ρ, Tendsto (fun η : ℝ => (freeConvST (vOU d N τs E₀ ω)
          (ouZeta ((Gauss.band d).tPow τs N)) ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ) ∧
        |ρ - rhoSc E₀| ≤ msize d N ^ (-step1Rate τs) := by
  obtain ⟨c₀, C₀, hc₀, hC₀, hFC⟩ := FreeConvStability.freeConv_stable_local hκ0
  have hκ'0 : 0 < min κ 1 := lt_min hκ0 one_pos
  have hc16 : 0 < c₀ / 16 := by positivity
  filter_upwards [step1_localErr_fc_sharp d h0 h1 hc16,
    step1_interp_slack_rate d (κ := κ) (ρ := step1Eps τs) (τs := τs) hκ0
      (by unfold step1Eps; linarith) h1,
    step1_tPow_eventually_le d h1 hc₀,
    step1_tPow_eventually_le d h1 (show (0 : ℝ) < 1 / 2 by norm_num),
    step1_tPow_eventually_le d h1 (show (0 : ℝ) < 7 * κ / 96 by linarith),
    step1_rpow_neg_eventually_le d (e := -step1Rate τs) (by unfold step1Rate; linarith)
      (c := c₀ * C₀) (by positivity),
    step1_rpow_neg_eventually_le d (e := -(3 * τs / 4)) (by linarith) (c := c₀ / 8)
      (by positivity),
    step1_rpow_neg_eventually_le d (e := -2 - τs) (by linarith) (c := c₀ / 16) hc16,
    step1_rpow_neg_eventually_le d (e := -(τs / 64)) (by linarith) (c := (4 * C₀)⁻¹)
      (by positivity)]
    with N hrate hslack htc0 hthalf htκ hεc hg8 hcube hC4
  intro ω hgood
  set t := (Gauss.band d).tPow τs N with ht_def
  set a := ouBandCoeff t with ha_def
  set ζ := ouZeta t with hζ_def
  set M := msize d N with hM_def
  set g := M ^ (-1 + step1Eps τs) with hg_def
  have hMpos : 0 < M := step1_msize_pos d N
  have htpos : 0 < t := step1_tPow_pos d τs N
  have ht1 : t ≤ 1 := by linarith
  have hapos : 0 < a := step1_ouBandCoeff_pos t
  have ha_le1 : a ≤ 1 := step1_ouBandCoeff_le_one htpos.le
  have hainv : a⁻¹ ≤ 2 := (step1_ouBandCoeff_inv_le htpos.le ht1).trans (by linarith)
  have hζpos : 0 < ζ := step1_ouZeta_pos htpos
  have hζc₀ : ζ ≤ c₀ := (step1_ouZeta_le htpos.le).trans htc0
  have hζge : t / 2 ≤ ζ := step1_ouZeta_ge_half htpos.le ht1
  have htM : t = M ^ (-1 + τs) := step1_tPow_eq d τs N
  have hgpos : 0 < g := Real.rpow_pos_of_pos hMpos _
  have hg_lt : g < 1 / 2 := step1_g_lt_half d N h0 h1
  -- `g ≤ (c₀/8) M^{-1+τ_*} ≤ c₀ ζ/4`
  have hg_le : g ≤ c₀ / 8 * M ^ (-1 + τs) := by
    have heq : g = M ^ (-(3 * τs / 4)) * M ^ (-1 + τs) := by
      rw [hg_def, ← Real.rpow_add hMpos]; unfold step1Eps; ring_nf
    rw [heq]
    exact mul_le_mul_of_nonneg_right hg8 (Real.rpow_nonneg hMpos.le _)
  have hlow : c₀ / 8 * M ^ (-1 + τs) ≤ c₀ * ζ / 4 := by
    rw [← htM]; nlinarith
  have hM3 : (M ^ 3)⁻¹ ≤ c₀ / 16 * M ^ (-1 + τs) := by
    rw [step1_inv_cube_eq d N τs]
    exact mul_le_mul_of_nonneg_right hcube (Real.rpow_nonneg hMpos.le _)
  set ε : ℝ := M ^ (-step1Rate τs) / C₀ with hε_def
  have hε0 : 0 ≤ ε := div_nonneg (Real.rpow_nonneg hMpos.le _) hC₀.le
  have hεc₀ : ε ≤ c₀ := by
    rw [hε_def, div_le_iff₀ hC₀]; exact hεc
  -- The closeness hypothesis of `freeConv_stable_local`.
  have hclose : ∀ w : ℂ, |w.re| ≤ min κ 1 / 16 → c₀ * ζ / 4 ≤ w.im → w.im ≤ 1 / 2 →
      ‖stieltjesVec (vOU d N τs E₀ ω) w - (Real.sqrt (1 - ζ) : ℂ)⁻¹ *
        msc ((Real.sqrt (1 - ζ) : ℂ)⁻¹ * (w + E₀))‖ ≤ ε := by
    intro w hβmem hηlo hη1
    set β := w.re with hβ_def
    set η := w.im with hη_def
    have hηg : g ≤ η := hg_le.trans (hlow.trans hηlo)
    have hηpos : 0 < η := lt_of_lt_of_le hgpos hηg
    obtain ⟨hβl, hβr⟩ := abs_le.mp hβmem
    obtain ⟨p, hp⟩ := step1_grid_exists (a := -(min κ 1 / 16)) (b := min κ 1 / 16)
      (by linarith) (step1_bC_pos κ M) hβl hβr
    obtain ⟨q, hq⟩ := step1_grid_exists (a := g) (b := (1 : ℝ) / 2) hg_lt
      (step1_hC_pos M) hηg hη1
    have hbeq : min κ 1 / 16 - -(min κ 1 / 16) = min κ 1 / 8 := by ring
    rw [hbeq] at hp
    have hβsp : |β - step1_betaGrid κ M p| ≤ (M ^ 3)⁻¹ :=
      hp.trans (step1_betaGrid_spacing κ M hκ0 hMpos)
    have hηsp : |η - step1_etaGrid M g q| ≤ (M ^ 3)⁻¹ :=
      hq.trans (step1_etaGrid_spacing M g hMpos hgpos.le hg_lt.le)
    set βg := step1_betaGrid κ M p with hβg_def
    set ηg := step1_etaGrid M g q with hηg_def
    have hβgmem : |βg| ≤ min κ 1 / 16 := step1_betaGrid_mem κ M hκ0 p
    have hηgmem : g ≤ ηg ∧ ηg ≤ 1 / 2 := step1_etaGrid_mem M g hg_lt.le q
    have hηgpos : 0 < ηg := lt_of_lt_of_le hgpos hηgmem.1
    -- The grid point sits at height `≥ (c₀/16) M^{-1+τ_*}`.
    have hηg_lo : c₀ / 16 * M ^ (-1 + τs) ≤ ηg := by
      have h1' := (abs_le.mp hηsp).2
      have h2' : c₀ / 8 * M ^ (-1 + τs) ≤ η := hlow.trans hηlo
      linarith
    have hgg : ‖RBM.stieltjes (Xmat d N ω) (step1_zGrid d κ τs E₀ N (p, q)) -
          msc (step1_zGrid d κ τs E₀ N (p, q))‖ ≤
        ((Gauss.band d).W N : ℝ) ^ step1Prec τs *
          ((Gauss.band d).zScale N (step1_zGrid d κ τs E₀ N (p, q)))⁻¹ :=
      Set.mem_iInter.mp hgood (p, q)
    have hzg_eq : step1_zGrid d κ τs E₀ N (p, q) = step1_zAt t E₀ βg ηg := rfl
    rw [hzg_eq] at hgg
    have hzgim_pos : 0 < (step1_zAt t E₀ βg ηg).im := step1_zAt_pos_im t E₀ βg ηg hηgpos
    have hzgim_ge : c₀ / 16 * M ^ (-1 + τs) ≤ (step1_zAt t E₀ βg ηg).im := by
      rw [step1_zAt_im]
      have : ηg ≤ ηg / a := by
        rw [le_div_iff₀ hapos]; exact mul_le_of_le_one_right hηgpos.le ha_le1
      linarith
    have hggb : ‖RBM.stieltjes (Xmat d N ω) (step1_zAt t E₀ βg ηg) -
        msc (step1_zAt t E₀ βg ηg)‖ ≤ M ^ (-(25 * τs / 64)) :=
      hgg.trans (hrate _ hzgim_pos hzgim_ge)
    have hdiff := step1_interp_diff d N ω (t := t) (E₀ := E₀) (β := β) (η := η)
      (βg := βg) (ηg := ηg) (κ := κ) hκ0 hκ2 hE₀ htpos.le ht1 htκ hβmem hβgmem
      (θ := g) hgpos hηg hηgmem.1 hη1 hηgmem.2 hβsp hηsp
    have herr : ‖RBM.stieltjes (Xmat d N ω) (step1_zAt t E₀ β η) -
        msc (step1_zAt t E₀ β η)‖ ≤ 2 * M ^ (-(25 * τs / 64)) := by
      have heq : RBM.stieltjes (Xmat d N ω) (step1_zAt t E₀ β η) - msc (step1_zAt t E₀ β η) =
          ((RBM.stieltjes (Xmat d N ω) (step1_zAt t E₀ β η) - msc (step1_zAt t E₀ β η)) -
              (RBM.stieltjes (Xmat d N ω) (step1_zAt t E₀ βg ηg) -
                msc (step1_zAt t E₀ βg ηg))) +
            (RBM.stieltjes (Xmat d N ω) (step1_zAt t E₀ βg ηg) - msc (step1_zAt t E₀ βg ηg)) := by
        ring
      rw [heq]
      refine (norm_add_le _ _).trans ?_
      have hs : 6 * (M ^ 3)⁻¹ * (g⁻¹ ^ 2 + 12 / min κ 1) ≤ M ^ (-(25 * τs / 64)) := hslack
      linarith [hdiff.trans hs, hggb]
    -- Rewrite the closeness quantity as `a⁻¹ (m_X(z) - m_sc(z))`.
    have hsq : Real.sqrt (1 - ζ) = a := (step1_ouBandCoeff_eq_sqrt).symm
    have hw_eq : w = (⟨β, η⟩ : ℂ) := (Complex.eta w).symm
    have hvec := step1_vOU_stieltjesVec_eq d N τs E₀ ω (w := w) hηpos
    have harg : ((a : ℝ) : ℂ)⁻¹ * (w + E₀) = step1_zAt t E₀ β η := by
      unfold step1_zAt
      congr 1
      apply Complex.ext <;> simp [hβ_def, hη_def]
    rw [hsq, hvec, harg, ← mul_sub, norm_mul, norm_inv, Complex.norm_real,
      Real.norm_of_nonneg hapos.le]
    have hbound : a⁻¹ * ‖RBM.stieltjes (Xmat d N ω) (step1_zAt t E₀ β η) -
        msc (step1_zAt t E₀ β η)‖ ≤ 2 * (2 * M ^ (-(25 * τs / 64))) :=
      mul_le_mul hainv herr (norm_nonneg _) (by norm_num)
    refine hbound.trans ?_
    -- `4 M^{-25τ_*/64} ≤ M^{-3τ_*/8} / C₀`
    have hsplit : M ^ (-(25 * τs / 64)) = M ^ (-(τs / 64)) * M ^ (-step1Rate τs) := by
      rw [← Real.rpow_add hMpos]; unfold step1Rate; ring_nf
    rw [hsplit, hε_def, le_div_iff₀ hC₀]
    have hR : 0 ≤ M ^ (-step1Rate τs) := Real.rpow_nonneg hMpos.le _
    have h4 : 4 * C₀ * M ^ (-(τs / 64)) ≤ 1 := by
      calc 4 * C₀ * M ^ (-(τs / 64)) ≤ 4 * C₀ * (4 * C₀)⁻¹ :=
            mul_le_mul_of_nonneg_left hC4 (by positivity)
        _ = 1 := mul_inv_cancel₀ (by positivity)
    have h5 := mul_le_mul_of_nonneg_right h4 hR
    calc 2 * (2 * (M ^ (-(τs / 64)) * M ^ (-step1Rate τs))) * C₀ =
        4 * C₀ * M ^ (-(τs / 64)) * M ^ (-step1Rate τs) := by ring
      _ ≤ 1 * M ^ (-step1Rate τs) := h5
      _ = M ^ (-step1Rate τs) := one_mul _
  obtain ⟨ρ, hρlim, hρclose, -⟩ :=
    hFC (vOU d N τs E₀ ω) (1 - ζ) ζ E₀ ε hζpos hζc₀ rfl hE₀ hε0 hεc₀ hclose
  refine ⟨ρ, hρlim, hρclose.trans (le_of_eq ?_)⟩
  rw [hε_def]; field_simp

/-! ### The good event of Step 1 -/

open scoped Matrix.Norms.L2Operator in
/-- **The regularity event**: with probability `≥ 1 - N^{-D}`, the diagonal
`v = e^{-t_*/2} λ(H) - E₀` is `(g, G)`-regular in the sense of [51, Definition 2.1] with
`g = M^{-1+τ_*/4}`, `G = M^{-σ}`, `c = cBulk κ`, `C = 2`, `CV = 1`, and the free-convolution
density `ρ_fc,ζ(t_*)(0)` exists and is `M^{-3τ_*/8}`-close to `ρ_sc(E₀)`.  The averaged band local
law `hLL` is a hypothesis. -/
theorem eventually_step1Good (d : Dims) {κ : ℝ} (hκ : 0 < κ)
    (hLL : BandTracialLocalLaw d (κ / 2)) {τs : ℝ} (h0 : 0 < τs) (h1 : τs < 1) {E₀ : ℝ} (hE₀ : |E₀| ≤ 2 - κ) (D : ℝ) :
    ∀ᶠ N in atTop, P d {ω |
      ¬ (IsRegular51 (vOU d N τs E₀ ω) (msize d N ^ (-1 + step1Eps τs))
          (msize d N ^ (-step1Sig τs)) (cBulk κ) 2 1 ∧
        ∃ ρ, Tendsto (fun η : ℝ => (freeConvST (vOU d N τs E₀ ω)
            (ouZeta ((Gauss.band d).tPow τs N)) ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ) ∧
          |ρ - rhoSc E₀| ≤ msize d N ^ (-step1Rate τs))} ≤ ENNReal.ofReal ((N:ℝ) ^ (-D)) := by
  have hκ2 : κ ≤ 2 := by linarith [abs_nonneg E₀]
  have hHP := (step1_gridGood_highProb d hκ hκ2 hLL h0 h1 hE₀).inter (step1_opNorm_highProb d)
  have hD' : (0 : ℝ) < max D 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  filter_upwards [hHP (max D 1) hD', step1_reg_eventually d hκ hκ2 hLL h0 h1 hE₀,
    step1_fc_eventually d hκ hκ2 h0 h1 hE₀, eventually_ge_atTop 1] with N hP hreg hfc hN1
  have hsub : {ω | ¬ (IsRegular51 (vOU d N τs E₀ ω) (msize d N ^ (-1 + step1Eps τs))
          (msize d N ^ (-step1Sig τs)) (cBulk κ) 2 1 ∧
        ∃ ρ, Tendsto (fun η : ℝ => (freeConvST (vOU d N τs E₀ ω)
            (ouZeta ((Gauss.band d).tPow τs N)) ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ) ∧
          |ρ - rhoSc E₀| ≤ msize d N ^ (-step1Rate τs))} ⊆
      ((⋂ k : Fin (step1_bC κ (msize d N) + 1) × Fin (step1_hC (msize d N) + 1),
        {ω | ‖RBM.stieltjes (Xmat d N ω) (step1_zGrid d κ τs E₀ N k) -
            msc (step1_zGrid d κ τs E₀ N k)‖ ≤
          ((Gauss.band d).W N : ℝ) ^ step1Prec τs *
            ((Gauss.band d).zScale N (step1_zGrid d κ τs E₀ N k))⁻¹}) ∩
        {ω | ‖Xmat d N ω‖ ≤ (N : ℝ) ^ ((1 : ℝ) / 2)})ᶜ := by
    intro ω hω hin
    exact hω ⟨hreg ω hin.1 hin.2, hfc ω hin.1⟩
  have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  calc _ ≤ _ := measure_mono hsub
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-max D 1)) := hP
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) :=
        ENNReal.ofReal_le_ofReal
          (Real.rpow_le_rpow_of_exponent_le hN1' (by linarith [le_max_left D 1]))

/-! ### Satisfiability notes -/

/-- **The good event is non-empty** (under `hLL`): eventually some `ω` realizes regularity and the
free-convolution closeness simultaneously (its probability is `≥ 1 - N^{-1}`). -/
theorem Step1Regularity.eventually_exists_step1Good (d : Dims) {κ : ℝ} (hκ : 0 < κ)
    (hLL : BandTracialLocalLaw d (κ / 2)) {τs : ℝ} (h0 : 0 < τs) (h1 : τs < 1) {E₀ : ℝ}
    (hE₀ : |E₀| ≤ 2 - κ) :
    ∀ᶠ N in atTop, ∃ ω : Ω d,
      IsRegular51 (vOU d N τs E₀ ω) (msize d N ^ (-1 + step1Eps τs))
          (msize d N ^ (-step1Sig τs)) (cBulk κ) 2 1 ∧
        ∃ ρ, Tendsto (fun η : ℝ => (freeConvST (vOU d N τs E₀ ω)
            (ouZeta ((Gauss.band d).tPow τs N)) ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ) ∧
          |ρ - rhoSc E₀| ≤ msize d N ^ (-step1Rate τs) := by
  filter_upwards [eventually_step1Good d hκ hLL h0 h1 hE₀ 1, eventually_ge_atTop 2]
    with N hN hN2
  by_contra hnone
  push Not at hnone
  have huniv : {ω : Ω d | ¬ (IsRegular51 (vOU d N τs E₀ ω) (msize d N ^ (-1 + step1Eps τs))
          (msize d N ^ (-step1Sig τs)) (cBulk κ) 2 1 ∧
        ∃ ρ, Tendsto (fun η : ℝ => (freeConvST (vOU d N τs E₀ ω)
            (ouZeta ((Gauss.band d).tPow τs N)) ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ) ∧
          |ρ - rhoSc E₀| ≤ msize d N ^ (-step1Rate τs))} = Set.univ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true, not_and, not_exists]
    exact fun hr ρ hρ => not_le.mpr (hnone ω hr ρ hρ)
  rw [huniv, measure_univ] at hN
  have hN2' : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
  have hlt : (N : ℝ) ^ (-(1 : ℝ)) < 1 := by
    rw [Real.rpow_neg_one]; exact inv_lt_one_of_one_lt₀ (by linarith)
  have := (ENNReal.one_le_ofReal).mp hN
  linarith

end RBM.Gauss

