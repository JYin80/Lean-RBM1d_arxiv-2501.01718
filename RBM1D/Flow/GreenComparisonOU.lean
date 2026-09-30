/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Flow.OUCommonFlow
import RBM1D.Flow.OUGenerator
import RBM1D.Flow.OUComparisonKernelBound
import RBM1D.Defs.MatrixMeasurable

/-!
# (2.25) on the common carrier

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, (2.25) in the proof of Theorem 2.6.  Assembles `eq225` from three pieces:

* `RBM.Gauss.ouCommon_integral_sub_eq`: the FTC form of the generator identity,
* `RBM.Gauss.testFun'_stieltjesImProduct`: `∏ Im m(z_i)` is a `TestFun'`,
* `RBM.centeredVariance_wirtProduct_kernel_bound` (`Flow/OUComparisonKernelBound.lean`):
  the deterministic pointwise bound of the generator's integrand by the positive-weight
  `paperL1Kernel`/`paperL2Kernel` sums.

The per-time hypothesis `hB` is an expectation bound; connecting it to the generator identity's
time integral needs (i) integrability of each `wirtSecond` term (from a global bound on the
second derivative of the Hermitian regularisation, transported at Hermitian points), and (ii)
integrability of the `hB` integrand itself (from a crude, non-sharp bound on `paperL1Kernel` /
`paperL2Kernel` and on `Im m`, uniform over Hermitian matrices, at the fixed spectral parameters
`z i`). Only existence of *some* finite bound is needed for (ii); the sharp constant comes from
`hB` itself.

No `sorry`, no `axiom`.
-/

namespace RBM.Gauss

open MeasureTheory Filter Matrix
open scoped ComplexConjugate Matrix.Norms.L2Operator

/-! ## 1. A global bound on `wirtSecond` for the Hermitian regularisation -/

private theorem gco_norm_coordD2_le {d : Dims} {N : ℕ} {Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}
    {M : Matrix (d.Idx N) (d.Idx N) ℂ} {C : ℝ} (hC : ‖fderiv ℝ (fderiv ℝ Φ) M‖ ≤ C)
    (p : d.Idx N × d.Idx N × Bool) :
    ‖coordD2 d N Φ M p‖ ≤ C * ‖Bmat d N p.1 p.2.1 p.2.2‖ * ‖Bmat d N p.1 p.2.1 p.2.2‖ :=
  le_trans ((fderiv ℝ (fderiv ℝ Φ) M (Bmat d N p.1 p.2.1 p.2.2)).le_opNorm _)
    (mul_le_mul_of_nonneg_right
      (le_trans ((fderiv ℝ (fderiv ℝ Φ) M).le_opNorm _)
        (mul_le_mul_of_nonneg_right hC (norm_nonneg _))) (norm_nonneg _))

/-- Global bound (all `M`, not only Hermitian) on `wirtSecond` of a `TestFun`. Reproduces
`Flow/OUGenerator.lean`'s (private) `exists_bound_wirtSecond`. -/
private theorem gco_bound_wirtSecond {d : Dims} {N : ℕ}
    {Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} (hΦ : TestFun d N Φ) (a b : d.Idx N) :
    ∃ C : ℝ, ∀ M : Matrix (d.Idx N) (d.Idx N) ℂ, ‖wirtSecond d N Φ M a b‖ ≤ C := by
  obtain ⟨C₂, hC₂⟩ := hΦ.bdd₂
  rcases eq_or_ne a b with rfl | hab
  · exact ⟨C₂ * ‖Bmat d N a a true‖ * ‖Bmat d N a a true‖, fun M => by
      unfold wirtSecond
      rw [if_pos rfl]
      exact gco_norm_coordD2_le (hC₂ M) _⟩
  · refine ⟨(1 / 4 : ℝ) * (C₂ * ‖Bmat d N a b true‖ * ‖Bmat d N a b true‖
        + C₂ * ‖Bmat d N a b false‖ * ‖Bmat d N a b false‖), fun M => ?_⟩
    unfold wirtSecond
    rw [if_neg hab]
    calc ‖(1 / 4 : ℝ) • (coordD2 d N Φ M (a, b, true) + coordD2 d N Φ M (a, b, false))‖
        = (1 / 4 : ℝ) *
            ‖coordD2 d N Φ M (a, b, true) + coordD2 d N Φ M (a, b, false)‖ := by
          rw [norm_smul]; simp
      _ ≤ (1 / 4 : ℝ) * (‖coordD2 d N Φ M (a, b, true)‖ + ‖coordD2 d N Φ M (a, b, false)‖) := by
          gcongr
          exact norm_add_le _ _
      _ ≤ _ := by
          gcongr
          · exact gco_norm_coordD2_le (hC₂ M) _
          · exact gco_norm_coordD2_le (hC₂ M) _

/-- Global continuity (all `M`) of `wirtSecond` of a `TestFun`. -/
private theorem gco_continuous_wirtSecond {d : Dims} {N : ℕ}
    {Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} (hΦ : TestFun d N Φ) (a b : d.Idx N) :
    Continuous fun M : Matrix (d.Idx N) (d.Idx N) ℂ => wirtSecond d N Φ M a b := by
  rcases eq_or_ne a b with rfl | hab
  · have heq : (fun M : Matrix (d.Idx N) (d.Idx N) ℂ => wirtSecond d N Φ M a a)
        = fun M => coordD2 d N Φ M (a, a, true) :=
      funext fun M => by unfold wirtSecond; rw [if_pos rfl]
    rw [heq]
    exact (hΦ.continuous_fderiv2.clm_apply continuous_const).clm_apply continuous_const
  · have heq : (fun M : Matrix (d.Idx N) (d.Idx N) ℂ => wirtSecond d N Φ M a b)
        = fun M => (1 / 4 : ℝ) • (coordD2 d N Φ M (a, b, true) + coordD2 d N Φ M (a, b, false)) :=
      funext fun M => by unfold wirtSecond; rw [if_neg hab]
    rw [heq]
    exact (((hΦ.continuous_fderiv2.clm_apply continuous_const).clm_apply continuous_const).add
      ((hΦ.continuous_fderiv2.clm_apply continuous_const).clm_apply
        continuous_const)).const_smul (1 / 4 : ℝ)

/-- Each `wirtSecond` term along the common flow is integrable. -/
private theorem gco_integrable_wirtSecond {d : Dims} {N : ℕ}
    {Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} (hΦ : TestFun' d N Φ) (t : ℝ) (a b : d.Idx N) :
    Integrable (fun ω => wirtSecond d N Φ ((ouCommonFlow d).Ht N t ω) a b)
      (ouCommonMeasure d) := by
  obtain ⟨C, hC⟩ := gco_bound_wirtSecond hΦ.herm a b
  have hcont : Continuous fun M : Matrix (d.Idx N) (d.Idx N) ℂ =>
      wirtSecond d N (hermFun d N Φ) M a b := gco_continuous_wirtSecond hΦ.herm a b
  have hmeas : Measurable
      (fun ω => wirtSecond d N (hermFun d N Φ) ((ouCommonFlow d).Ht N t ω) a b) :=
    hcont.measurable.comp (ouCommonFlow_measurable d N t)
  have heq : (fun ω => wirtSecond d N Φ ((ouCommonFlow d).Ht N t ω) a b)
      = fun ω => wirtSecond d N (hermFun d N Φ) ((ouCommonFlow d).Ht N t ω) a b := by
    funext ω
    exact (wirtSecond_hermFun ((ouCommonFlow d).hermitian N t ω)
      (hΦ.contDiffAt _ ((ouCommonFlow d).hermitian N t ω)) a b).symm
  rw [heq]
  exact Integrable.of_bound hmeas.aestronglyMeasurable C (Eventually.of_forall fun ω => hC _)

/-! ## 2. Sum/integral swap for the double sum over `d.Idx N` -/

/-- `∑ a b, c_ab • ∫ ω, wirtSecond a b ∂μ = ∫ ω, ∑ a b, c_ab * wirtSecond a b ∂μ`. -/
private theorem gco_sum_integral_swap {d : Dims} {N : ℕ}
    {Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} (hΦ : TestFun' d N Φ) (t : ℝ) :
    ∑ a : d.Idx N, ∑ b : d.Idx N, (RBM.centeredVarianceEntry d N a b : ℂ) *
        ∫ ω, wirtSecond d N Φ ((ouCommonFlow d).Ht N t ω) a b ∂(ouCommonMeasure d) =
      ∫ ω, ∑ a : d.Idx N, ∑ b : d.Idx N, (RBM.centeredVarianceEntry d N a b : ℂ) *
        wirtSecond d N Φ ((ouCommonFlow d).Ht N t ω) a b ∂(ouCommonMeasure d) := by
  have hb : ∀ a : d.Idx N, (∑ b : d.Idx N, (RBM.centeredVarianceEntry d N a b : ℂ) *
        ∫ ω, wirtSecond d N Φ ((ouCommonFlow d).Ht N t ω) a b ∂(ouCommonMeasure d)) =
      ∫ ω, ∑ b : d.Idx N, (RBM.centeredVarianceEntry d N a b : ℂ) *
        wirtSecond d N Φ ((ouCommonFlow d).Ht N t ω) a b ∂(ouCommonMeasure d) := by
    intro a
    have hterm : ∀ b : d.Idx N, (RBM.centeredVarianceEntry d N a b : ℂ) *
          ∫ ω, wirtSecond d N Φ ((ouCommonFlow d).Ht N t ω) a b ∂(ouCommonMeasure d) =
        ∫ ω, (RBM.centeredVarianceEntry d N a b : ℂ) *
          wirtSecond d N Φ ((ouCommonFlow d).Ht N t ω) a b ∂(ouCommonMeasure d) := by
      intro b
      rw [MeasureTheory.integral_const_mul]
    rw [Finset.sum_congr rfl fun b _ => hterm b,
      MeasureTheory.integral_finsetSum Finset.univ
        (fun b _ => (gco_integrable_wirtSecond hΦ t a b).const_mul _)]
  rw [Finset.sum_congr rfl fun a _ => hb a,
    MeasureTheory.integral_finsetSum Finset.univ
      (fun a _ => integrable_finsetSum Finset.univ
        (fun b _ => (gco_integrable_wirtSecond hΦ t a b).const_mul _))]

/-! ## 3. A crude, uniform-in-Hermitian-`H` bound on the (2.25) kernel integrand -/

private theorem gco_norm_signedGreen_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : 0 < z.im) (σ : Bool) :
    ‖RBM.signedGreen H z σ‖ ≤ z.im⁻¹ := by
  cases σ
  · have h : RBM.signedGreen H z false = green H (starRingEnd ℂ z) := rfl
    rw [h]
    refine norm_green_le hH hz ?_
    rw [Complex.conj_im, abs_neg]
    exact le_abs_self z.im
  · have h : RBM.signedGreen H z true = green H z := rfl
    rw [h]
    exact norm_green_le hH hz (le_abs_self z.im)

private theorem gco_norm_centeredVarianceEntry_le (d : Dims) (N : ℕ) (a b : d.Idx N) :
    ‖(RBM.centeredVarianceEntry d N a b : ℂ)‖ ≤ 2 := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  have hnat : ∀ k : ℕ, (k : ℝ)⁻¹ ≤ 1 := by
    intro k
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · simp [h0]
    · exact inv_le_one_of_one_le₀ (by exact_mod_cast hpos)
  have h1 : RBM.Sblk (d.L N) (d.W N) a b ≤ 1 := by
    refine (RBM.Sblk_le a b).trans ?_
    split_ifs
    · exact hnat (d.W N)
    · norm_num
  have h2 : (0 : ℝ) ≤ RBM.Sblk (d.L N) (d.W N) a b := RBM.Sblk_nonneg a b
  have h3 := hnat (Fintype.card (d.Idx N))
  have h4 : (0 : ℝ) ≤ (Fintype.card (d.Idx N) : ℝ)⁻¹ := by positivity
  unfold RBM.centeredVarianceEntry
  rw [abs_le]
  constructor <;> linarith

/-- Submultiplicative crude bound on `paperK1Contraction`, valid for every Hermitian `H`, uniform
in the sign choices `σ, τ`. -/
private theorem gco_norm_paperK1_le {d : Dims} {N : ℕ} {H : Matrix (d.Idx N) (d.Idx N) ℂ}
    (hH : H.IsHermitian) {z : ℂ} (hz : 0 < z.im) (σ τ : Bool) :
    ‖RBM.paperK1Contraction N H z σ τ‖ ≤
      (Fintype.card (d.Idx N) : ℝ) ^ 2 * (2 * z.im⁻¹ ^ 3) := by
  have hcardnorm : ‖((Fintype.card (d.Idx N) : ℂ)⁻¹)‖ ≤ 1 := by
    rw [norm_inv]
    have : ‖((Fintype.card (d.Idx N) : ℕ) : ℂ)‖ = (Fintype.card (d.Idx N) : ℝ) := by
      rw [Complex.norm_natCast]
    rw [this]
    rcases Nat.eq_zero_or_pos (Fintype.card (d.Idx N)) with h0 | hpos
    · simp [h0]
    · exact inv_le_one_of_one_le₀ (by exact_mod_cast hpos)
  unfold RBM.paperK1Contraction
  rw [norm_mul]
  have hterm : ∀ a b : d.Idx N,
      ‖(RBM.signedGreen H z σ * RBM.signedGreen H z σ) a a *
        (RBM.centeredVarianceEntry d N a b : ℂ) * RBM.signedGreen H z τ b b‖ ≤
      2 * z.im⁻¹ ^ 3 := by
    intro a b
    have h1 : ‖(RBM.signedGreen H z σ * RBM.signedGreen H z σ) a a‖ ≤ z.im⁻¹ * z.im⁻¹ := by
      refine (RBM.norm_apply_le_l2_opNorm _ a a).trans ?_
      refine (norm_mul_le _ _).trans ?_
      exact mul_le_mul (gco_norm_signedGreen_le hH hz σ) (gco_norm_signedGreen_le hH hz σ)
        (norm_nonneg _) (by positivity)
    have h2 := gco_norm_centeredVarianceEntry_le d N a b
    have h3 : ‖RBM.signedGreen H z τ b b‖ ≤ z.im⁻¹ :=
      (RBM.norm_apply_le_l2_opNorm _ b b).trans (gco_norm_signedGreen_le hH hz τ)
    calc ‖(RBM.signedGreen H z σ * RBM.signedGreen H z σ) a a *
          (RBM.centeredVarianceEntry d N a b : ℂ) * RBM.signedGreen H z τ b b‖
        = ‖(RBM.signedGreen H z σ * RBM.signedGreen H z σ) a a‖ *
            ‖(RBM.centeredVarianceEntry d N a b : ℂ)‖ * ‖RBM.signedGreen H z τ b b‖ := by
          rw [norm_mul, norm_mul]
      _ ≤ (z.im⁻¹ * z.im⁻¹) * 2 * z.im⁻¹ := by
          gcongr
      _ = 2 * z.im⁻¹ ^ 3 := by ring
  have hsum : ‖∑ a : d.Idx N, ∑ b : d.Idx N,
      (RBM.signedGreen H z σ * RBM.signedGreen H z σ) a a *
        (RBM.centeredVarianceEntry d N a b : ℂ) * RBM.signedGreen H z τ b b‖ ≤
      (Fintype.card (d.Idx N) : ℝ) ^ 2 * (2 * z.im⁻¹ ^ 3) := by
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun a _ => norm_sum_le _ _).trans ?_
    calc ∑ a : d.Idx N, ∑ b : d.Idx N,
        ‖(RBM.signedGreen H z σ * RBM.signedGreen H z σ) a a *
          (RBM.centeredVarianceEntry d N a b : ℂ) * RBM.signedGreen H z τ b b‖
        ≤ ∑ _a : d.Idx N, ∑ _b : d.Idx N, 2 * z.im⁻¹ ^ 3 :=
          Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hterm a b
      _ = (Fintype.card (d.Idx N) : ℝ) ^ 2 * (2 * z.im⁻¹ ^ 3) := by
          simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
          ring
  calc ‖((Fintype.card (d.Idx N) : ℂ)⁻¹)‖ *
      ‖∑ a : d.Idx N, ∑ b : d.Idx N, (RBM.signedGreen H z σ * RBM.signedGreen H z σ) a a *
          (RBM.centeredVarianceEntry d N a b : ℂ) * RBM.signedGreen H z τ b b‖
      ≤ 1 * ((Fintype.card (d.Idx N) : ℝ) ^ 2 * (2 * z.im⁻¹ ^ 3)) := by
        gcongr
    _ = (Fintype.card (d.Idx N) : ℝ) ^ 2 * (2 * z.im⁻¹ ^ 3) := by ring

private theorem gco_norm_paperK2_le {d : Dims} {N : ℕ} {H : Matrix (d.Idx N) (d.Idx N) ℂ}
    (hH : H.IsHermitian) {z₁ z₂ : ℂ} (hz₁ : 0 < z₁.im) (hz₂ : 0 < z₂.im) (σ τ : Bool) :
    ‖RBM.paperK2Contraction N H z₁ z₂ σ τ‖ ≤
      (Fintype.card (d.Idx N) : ℝ) ^ 2 * (2 * (z₁.im⁻¹ ^ 2 * z₂.im⁻¹ ^ 2)) := by
  have hcardnorm : ‖((Fintype.card (d.Idx N) : ℂ)⁻¹)‖ ≤ 1 := by
    rw [norm_inv]
    have heq : ‖((Fintype.card (d.Idx N) : ℕ) : ℂ)‖ = (Fintype.card (d.Idx N) : ℝ) := by
      rw [Complex.norm_natCast]
    rw [heq]
    rcases Nat.eq_zero_or_pos (Fintype.card (d.Idx N)) with h0 | hpos
    · simp [h0]
    · exact inv_le_one_of_one_le₀ (by exact_mod_cast hpos)
  unfold RBM.paperK2Contraction
  have hterm : ∀ a b : d.Idx N,
      ‖(RBM.signedGreen H z₁ σ * RBM.signedGreen H z₁ σ) a b *
        (RBM.centeredVarianceEntry d N a b : ℂ) *
          (RBM.signedGreen H z₂ τ * RBM.signedGreen H z₂ τ) b a‖ ≤
      2 * (z₁.im⁻¹ ^ 2 * z₂.im⁻¹ ^ 2) := by
    intro a b
    have h1 : ‖(RBM.signedGreen H z₁ σ * RBM.signedGreen H z₁ σ) a b‖ ≤ z₁.im⁻¹ * z₁.im⁻¹ := by
      refine (RBM.norm_apply_le_l2_opNorm _ a b).trans ?_
      refine (norm_mul_le _ _).trans ?_
      exact mul_le_mul (gco_norm_signedGreen_le hH hz₁ σ) (gco_norm_signedGreen_le hH hz₁ σ)
        (norm_nonneg _) (by positivity)
    have h2 := gco_norm_centeredVarianceEntry_le d N a b
    have h3 : ‖(RBM.signedGreen H z₂ τ * RBM.signedGreen H z₂ τ) b a‖ ≤ z₂.im⁻¹ * z₂.im⁻¹ := by
      refine (RBM.norm_apply_le_l2_opNorm _ b a).trans ?_
      refine (norm_mul_le _ _).trans ?_
      exact mul_le_mul (gco_norm_signedGreen_le hH hz₂ τ) (gco_norm_signedGreen_le hH hz₂ τ)
        (norm_nonneg _) (by positivity)
    calc ‖(RBM.signedGreen H z₁ σ * RBM.signedGreen H z₁ σ) a b *
          (RBM.centeredVarianceEntry d N a b : ℂ) *
            (RBM.signedGreen H z₂ τ * RBM.signedGreen H z₂ τ) b a‖
        = ‖(RBM.signedGreen H z₁ σ * RBM.signedGreen H z₁ σ) a b‖ *
            ‖(RBM.centeredVarianceEntry d N a b : ℂ)‖ *
              ‖(RBM.signedGreen H z₂ τ * RBM.signedGreen H z₂ τ) b a‖ := by
          rw [norm_mul, norm_mul]
      _ ≤ (z₁.im⁻¹ * z₁.im⁻¹) * 2 * (z₂.im⁻¹ * z₂.im⁻¹) := by gcongr
      _ = 2 * (z₁.im⁻¹ ^ 2 * z₂.im⁻¹ ^ 2) := by ring
  have hsum : ‖∑ a : d.Idx N, ∑ b : d.Idx N,
      (RBM.signedGreen H z₁ σ * RBM.signedGreen H z₁ σ) a b *
        (RBM.centeredVarianceEntry d N a b : ℂ) *
          (RBM.signedGreen H z₂ τ * RBM.signedGreen H z₂ τ) b a‖ ≤
      (Fintype.card (d.Idx N) : ℝ) ^ 2 * (2 * (z₁.im⁻¹ ^ 2 * z₂.im⁻¹ ^ 2)) := by
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun a _ => norm_sum_le _ _).trans ?_
    calc ∑ a : d.Idx N, ∑ b : d.Idx N,
        ‖(RBM.signedGreen H z₁ σ * RBM.signedGreen H z₁ σ) a b *
          (RBM.centeredVarianceEntry d N a b : ℂ) *
            (RBM.signedGreen H z₂ τ * RBM.signedGreen H z₂ τ) b a‖
        ≤ ∑ _a : d.Idx N, ∑ _b : d.Idx N, 2 * (z₁.im⁻¹ ^ 2 * z₂.im⁻¹ ^ 2) :=
          Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hterm a b
      _ = (Fintype.card (d.Idx N) : ℝ) ^ 2 * (2 * (z₁.im⁻¹ ^ 2 * z₂.im⁻¹ ^ 2)) := by
          simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
          ring
  rw [norm_mul, norm_mul]
  calc ‖((Fintype.card (d.Idx N) : ℂ)⁻¹)‖ * ‖((Fintype.card (d.Idx N) : ℂ)⁻¹)‖ *
      ‖∑ a : d.Idx N, ∑ b : d.Idx N, (RBM.signedGreen H z₁ σ * RBM.signedGreen H z₁ σ) a b *
          (RBM.centeredVarianceEntry d N a b : ℂ) *
            (RBM.signedGreen H z₂ τ * RBM.signedGreen H z₂ τ) b a‖
      ≤ 1 * 1 * ((Fintype.card (d.Idx N) : ℝ) ^ 2 * (2 * (z₁.im⁻¹ ^ 2 * z₂.im⁻¹ ^ 2))) := by
        gcongr
    _ = (Fintype.card (d.Idx N) : ℝ) ^ 2 * (2 * (z₁.im⁻¹ ^ 2 * z₂.im⁻¹ ^ 2)) := by ring

private theorem gco_paperL1Kernel_le {d : Dims} {N : ℕ} {H : Matrix (d.Idx N) (d.Idx N) ℂ}
    (hH : H.IsHermitian) {z : ℂ} (hz : 0 < z.im) :
    RBM.paperL1Kernel d N H z ≤ 8 * (Fintype.card (d.Idx N) : ℝ) ^ 2 * z.im⁻¹ ^ 3 := by
  unfold RBM.paperL1Kernel
  calc ∑ σ : Bool, ∑ τ : Bool, ‖RBM.paperK1Contraction N H z σ τ‖
      ≤ ∑ _σ : Bool, ∑ _τ : Bool,
          (Fintype.card (d.Idx N) : ℝ) ^ 2 * (2 * z.im⁻¹ ^ 3) :=
        Finset.sum_le_sum fun σ _ =>
          Finset.sum_le_sum fun τ _ => gco_norm_paperK1_le hH hz σ τ
    _ = 8 * (Fintype.card (d.Idx N) : ℝ) ^ 2 * z.im⁻¹ ^ 3 := by
        simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_bool]
        ring

private theorem gco_paperL2Kernel_le {d : Dims} {N : ℕ} {H : Matrix (d.Idx N) (d.Idx N) ℂ}
    (hH : H.IsHermitian) {z₁ z₂ : ℂ} (hz₁ : 0 < z₁.im) (hz₂ : 0 < z₂.im) :
    RBM.paperL2Kernel d N H z₁ z₂ ≤
      8 * (Fintype.card (d.Idx N) : ℝ) ^ 2 * (z₁.im⁻¹ ^ 2 * z₂.im⁻¹ ^ 2) := by
  unfold RBM.paperL2Kernel
  calc ∑ σ : Bool, ∑ τ : Bool, ‖RBM.paperK2Contraction N H z₁ z₂ σ τ‖
      ≤ ∑ _σ : Bool, ∑ _τ : Bool,
          (Fintype.card (d.Idx N) : ℝ) ^ 2 * (2 * (z₁.im⁻¹ ^ 2 * z₂.im⁻¹ ^ 2)) :=
        Finset.sum_le_sum fun σ _ =>
          Finset.sum_le_sum fun τ _ => gco_norm_paperK2_le hH hz₁ hz₂ σ τ
    _ = 8 * (Fintype.card (d.Idx N) : ℝ) ^ 2 * (z₁.im⁻¹ ^ 2 * z₂.im⁻¹ ^ 2) := by
        simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_bool]
        ring

private theorem gco_norm_stieltjes_le {d : Dims} {N : ℕ} {H : Matrix (d.Idx N) (d.Idx N) ℂ}
    (hH : H.IsHermitian) {z : ℂ} (hz : 0 < z.im) :
    ‖RBM.stieltjes H z‖ ≤ (Fintype.card (d.Idx N) : ℝ) * z.im⁻¹ := by
  have hcardnorm : ‖((Fintype.card (d.Idx N) : ℂ)⁻¹)‖ ≤ 1 := by
    rw [norm_inv]
    have heq : ‖((Fintype.card (d.Idx N) : ℕ) : ℂ)‖ = (Fintype.card (d.Idx N) : ℝ) := by
      rw [Complex.norm_natCast]
    rw [heq]
    rcases Nat.eq_zero_or_pos (Fintype.card (d.Idx N)) with h0 | hpos
    · simp [h0]
    · exact inv_le_one_of_one_le₀ (by exact_mod_cast hpos)
  have htrace : ‖(green H z).trace‖ ≤ (Fintype.card (d.Idx N) : ℝ) * z.im⁻¹ := by
    unfold Matrix.trace Matrix.diag
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i : d.Idx N, ‖green H z i i‖
        ≤ ∑ _i : d.Idx N, z.im⁻¹ :=
          Finset.sum_le_sum fun i _ =>
            (RBM.norm_apply_le_l2_opNorm _ i i).trans (norm_green_le hH hz (le_abs_self z.im))
      _ = (Fintype.card (d.Idx N) : ℝ) * z.im⁻¹ := by
          rw [Finset.sum_const, Finset.card_univ]; ring
  unfold RBM.stieltjes
  rw [norm_mul]
  calc ‖((Fintype.card (d.Idx N) : ℂ)⁻¹)‖ * ‖(green H z).trace‖ ≤
      1 * ((Fintype.card (d.Idx N) : ℝ) * z.im⁻¹) := by gcongr
    _ = (Fintype.card (d.Idx N) : ℝ) * z.im⁻¹ := by ring

/-- A single, `ω`-independent finite bound `Zb ≥ 1` on `(z i).im⁻¹` for every `i`. -/
private theorem gco_exists_Zb {n : ℕ} (z : Fin n → ℂ) (hz : ∀ i, 0 < (z i).im) :
    ∃ Zb : ℝ, 1 ≤ Zb ∧ ∀ i, (z i).im⁻¹ ≤ Zb := by
  have hsnn : (0:ℝ) ≤ ∑ i, (z i).im⁻¹ :=
    Finset.sum_nonneg fun i _ => inv_nonneg.mpr (hz i).le
  refine ⟨1 + ∑ i, (z i).im⁻¹, by linarith, fun j => ?_⟩
  have : (z j).im⁻¹ ≤ ∑ i, (z i).im⁻¹ :=
    Finset.single_le_sum (f := fun i : Fin n => (z i).im⁻¹)
      (fun i _ => inv_nonneg.mpr (hz i).le) (Finset.mem_univ j)
  linarith

/-- The `hB` integrand, as a bare (unintegrated) function of `ω`. -/
private noncomputable def gco_RHSb (d : Dims) (N : ℕ) {n : ℕ} (z : Fin n → ℂ)
    (H : Matrix (d.Idx N) (d.Idx N) ℂ) : ℝ :=
  (∑ i, (∏ j ∈ Finset.univ.erase i, (RBM.stieltjes H (z j)).im) * RBM.paperL1Kernel d N H (z i)) +
    ∑ i, ∑ j ∈ Finset.univ.erase i,
      (∏ k ∈ (Finset.univ.erase i).erase j, (RBM.stieltjes H (z k)).im) *
        RBM.paperL2Kernel d N H (z i) (z j)

private theorem gco_abs_RHSb_le (d : Dims) (N : ℕ) {n : ℕ} (z : Fin n → ℂ)
    (hz : ∀ i, 0 < (z i).im) :
    ∃ C : ℝ, ∀ H' : Matrix (d.Idx N) (d.Idx N) ℂ, H'.IsHermitian → |gco_RHSb d N z H'| ≤ C := by
  obtain ⟨Zb, hZb1, hZb⟩ := gco_exists_Zb z hz
  set Q : ℝ := (Fintype.card (d.Idx N) : ℝ) with hQ
  set W : ℝ := max 1 (Q * Zb) with hW
  have hW1 : 1 ≤ W := le_max_left _ _
  have hQnn : (0:ℝ) ≤ Q := by rw [hQ]; positivity
  have hK : ∀ (H' : Matrix (d.Idx N) (d.Idx N) ℂ), H'.IsHermitian → ∀ i : Fin n,
      RBM.paperL1Kernel d N H' (z i) ≤ 8 * Q ^ 2 * Zb ^ 3 := by
    intro H' hH' i
    refine (gco_paperL1Kernel_le hH' (hz i)).trans ?_
    have h0 : (0:ℝ) ≤ (z i).im⁻¹ := inv_nonneg.mpr (hz i).le
    have hle : (z i).im⁻¹ ^ 3 ≤ Zb ^ 3 := pow_le_pow_left₀ h0 (hZb i) 3
    nlinarith [hle, sq_nonneg Q, hQnn]
  have hK2 : ∀ (H' : Matrix (d.Idx N) (d.Idx N) ℂ), H'.IsHermitian → ∀ i j : Fin n,
      RBM.paperL2Kernel d N H' (z i) (z j) ≤ 8 * Q ^ 2 * Zb ^ 4 := by
    intro H' hH' i j
    refine (gco_paperL2Kernel_le hH' (hz i) (hz j)).trans ?_
    have h0i : (0:ℝ) ≤ (z i).im⁻¹ := inv_nonneg.mpr (hz i).le
    have h0j : (0:ℝ) ≤ (z j).im⁻¹ := inv_nonneg.mpr (hz j).le
    have h1 : (z i).im⁻¹ ^ 2 ≤ Zb ^ 2 := pow_le_pow_left₀ h0i (hZb i) 2
    have h2 : (z j).im⁻¹ ^ 2 ≤ Zb ^ 2 := pow_le_pow_left₀ h0j (hZb j) 2
    have hZbnn : (0:ℝ) ≤ Zb := by linarith
    nlinarith [h1, h2, sq_nonneg Q, mul_le_mul h1 h2 (by positivity) (by positivity),
      hQnn, hZbnn]
  have hprod : ∀ (H' : Matrix (d.Idx N) (d.Idx N) ℂ), H'.IsHermitian →
      ∀ s : Finset (Fin n), |∏ j ∈ s, (RBM.stieltjes H' (z j)).im| ≤ W ^ n := by
    intro H' hH' s
    have hbound : ∀ j : Fin n, |(RBM.stieltjes H' (z j)).im| ≤ W := by
      intro j
      refine le_trans (Complex.abs_im_le_norm _) ?_
      refine (gco_norm_stieltjes_le hH' (hz j)).trans ?_
      have : Q * (z j).im⁻¹ ≤ Q * Zb := mul_le_mul_of_nonneg_left (hZb j) hQnn
      exact this.trans (le_max_right _ _)
    calc |∏ j ∈ s, (RBM.stieltjes H' (z j)).im| = ∏ j ∈ s, |(RBM.stieltjes H' (z j)).im| := by
          rw [Finset.abs_prod]
      _ ≤ ∏ _j ∈ s, W := Finset.prod_le_prod₀ (fun j _ => abs_nonneg _) (fun j _ => hbound j)
      _ = W ^ s.card := by rw [Finset.prod_const]
      _ ≤ W ^ n := by
          refine pow_le_pow_right₀ hW1 ?_
          calc s.card ≤ (Finset.univ : Finset (Fin n)).card :=
                Finset.card_le_card (Finset.subset_univ s)
            _ = n := by rw [Finset.card_univ, Fintype.card_fin]
  refine ⟨(n : ℝ) * W ^ n * (8 * Q ^ 2 * Zb ^ 4) + (n : ℝ) ^ 2 * W ^ n * (8 * Q ^ 2 * Zb ^ 4),
    fun H' hH' => ?_⟩
  unfold gco_RHSb
  have hnonneg : (0:ℝ) ≤ 8 * Q ^ 2 * Zb ^ 4 := by positivity
  have hterm1 : |∑ i : Fin n, (∏ j ∈ Finset.univ.erase i, (RBM.stieltjes H' (z j)).im) *
        RBM.paperL1Kernel d N H' (z i)| ≤ (n : ℝ) * W ^ n * (8 * Q ^ 2 * Zb ^ 4) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have : ∀ i : Fin n, |(∏ j ∈ Finset.univ.erase i, (RBM.stieltjes H' (z j)).im) *
        RBM.paperL1Kernel d N H' (z i)| ≤ W ^ n * (8 * Q ^ 2 * Zb ^ 4) := by
      intro i
      rw [abs_mul]
      have hp1 : |RBM.paperL1Kernel d N H' (z i)| = RBM.paperL1Kernel d N H' (z i) := by
        rw [abs_of_nonneg]
        unfold RBM.paperL1Kernel
        exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
      rw [hp1]
      have hL1nn : (0:ℝ) ≤ RBM.paperL1Kernel d N H' (z i) := by
        unfold RBM.paperL1Kernel
        exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
      have hWnnn : (0:ℝ) ≤ W ^ n := by positivity
      calc |∏ j ∈ Finset.univ.erase i, (RBM.stieltjes H' (z j)).im| *
          RBM.paperL1Kernel d N H' (z i) ≤ W ^ n * (8 * Q ^ 2 * Zb ^ 3) :=
            mul_le_mul (hprod H' hH' _) (hK H' hH' i) hL1nn hWnnn
        _ ≤ W ^ n * (8 * Q ^ 2 * Zb ^ 4) := by
            have : Zb ^ 3 ≤ Zb ^ 4 := by
              have : Zb ^ 3 * 1 ≤ Zb ^ 3 * Zb := mul_le_mul_of_nonneg_left hZb1 (by positivity)
              nlinarith [this]
            nlinarith [mul_le_mul_of_nonneg_left this (by positivity : (0:ℝ) ≤ W ^ n * (8 * Q ^ 2)),
              hWnnn]
    calc ∑ i : Fin n, |(∏ j ∈ Finset.univ.erase i, (RBM.stieltjes H' (z j)).im) *
          RBM.paperL1Kernel d N H' (z i)|
        ≤ ∑ _i : Fin n, W ^ n * (8 * Q ^ 2 * Zb ^ 4) := Finset.sum_le_sum fun i _ => this i
      _ = (n : ℝ) * W ^ n * (8 * Q ^ 2 * Zb ^ 4) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring
  have hterm2 : |∑ i : Fin n, ∑ j ∈ Finset.univ.erase i,
        (∏ k ∈ (Finset.univ.erase i).erase j, (RBM.stieltjes H' (z k)).im) *
          RBM.paperL2Kernel d N H' (z i) (z j)| ≤
      (n : ℝ) ^ 2 * W ^ n * (8 * Q ^ 2 * Zb ^ 4) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hinner : ∀ i : Fin n, |∑ j ∈ Finset.univ.erase i,
        (∏ k ∈ (Finset.univ.erase i).erase j, (RBM.stieltjes H' (z k)).im) *
          RBM.paperL2Kernel d N H' (z i) (z j)| ≤ (n : ℝ) * W ^ n * (8 * Q ^ 2 * Zb ^ 4) := by
      intro i
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have : ∀ j ∈ Finset.univ.erase i,
          |(∏ k ∈ (Finset.univ.erase i).erase j, (RBM.stieltjes H' (z k)).im) *
            RBM.paperL2Kernel d N H' (z i) (z j)| ≤ W ^ n * (8 * Q ^ 2 * Zb ^ 4) := by
        intro j _
        rw [abs_mul]
        have hp2 : |RBM.paperL2Kernel d N H' (z i) (z j)| =
            RBM.paperL2Kernel d N H' (z i) (z j) := by
          rw [abs_of_nonneg]
          unfold RBM.paperL2Kernel
          exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
        rw [hp2]
        exact mul_le_mul (hprod H' hH' _) (hK2 H' hH' i j) (by
          unfold RBM.paperL2Kernel
          exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
          (by positivity)
      calc ∑ j ∈ Finset.univ.erase i,
          |(∏ k ∈ (Finset.univ.erase i).erase j, (RBM.stieltjes H' (z k)).im) *
            RBM.paperL2Kernel d N H' (z i) (z j)|
          ≤ ∑ _j ∈ Finset.univ.erase i, W ^ n * (8 * Q ^ 2 * Zb ^ 4) :=
            Finset.sum_le_sum this
        _ ≤ (n : ℝ) * W ^ n * (8 * Q ^ 2 * Zb ^ 4) := by
            rw [Finset.sum_const]
            have : (Finset.univ.erase i).card ≤ n := by
              calc (Finset.univ.erase i).card ≤ (Finset.univ : Finset (Fin n)).card :=
                    Finset.card_le_card (Finset.erase_subset _ _)
                _ = n := by rw [Finset.card_univ, Fintype.card_fin]
            have hnn : (0:ℝ) ≤ W ^ n * (8 * Q ^ 2 * Zb ^ 4) := by positivity
            calc (Finset.univ.erase i).card • (W ^ n * (8 * Q ^ 2 * Zb ^ 4))
                ≤ (n : ℕ) • (W ^ n * (8 * Q ^ 2 * Zb ^ 4)) := by
                  exact nsmul_le_nsmul_left hnn this
              _ = (n : ℝ) * W ^ n * (8 * Q ^ 2 * Zb ^ 4) := by
                  rw [nsmul_eq_mul]; ring
    calc ∑ i : Fin n, |∑ j ∈ Finset.univ.erase i,
          (∏ k ∈ (Finset.univ.erase i).erase j, (RBM.stieltjes H' (z k)).im) *
            RBM.paperL2Kernel d N H' (z i) (z j)|
        ≤ ∑ _i : Fin n, (n : ℝ) * W ^ n * (8 * Q ^ 2 * Zb ^ 4) :=
          Finset.sum_le_sum fun i _ => hinner i
      _ = (n : ℝ) ^ 2 * W ^ n * (8 * Q ^ 2 * Zb ^ 4) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring
  calc |(∑ i : Fin n, (∏ j ∈ Finset.univ.erase i, (RBM.stieltjes H' (z j)).im) *
        RBM.paperL1Kernel d N H' (z i)) +
      ∑ i : Fin n, ∑ j ∈ Finset.univ.erase i,
        (∏ k ∈ (Finset.univ.erase i).erase j, (RBM.stieltjes H' (z k)).im) *
          RBM.paperL2Kernel d N H' (z i) (z j)|
      ≤ (n : ℝ) * W ^ n * (8 * Q ^ 2 * Zb ^ 4) + (n : ℝ) ^ 2 * W ^ n * (8 * Q ^ 2 * Zb ^ 4) :=
        (abs_add_le _ _).trans (add_le_add hterm1 hterm2)
    _ = _ := rfl

/-! ## 4. Measurability of the `hB` integrand along the flow -/

private theorem gco_measurable_green (d : Dims) (N : ℕ) (t : ℝ) (z : ℂ) (x y : d.Idx N) :
    Measurable fun ω => green ((ouCommonFlow d).Ht N t ω) z x y := by
  have hH := ouCommonFlow_measurable d N t
  have hM : Measurable fun ω => (ouCommonFlow d).Ht N t ω - z • (1 : Matrix _ _ ℂ) :=
    Measurable.of_eval_matrix _ fun a b => by
      simp only [Matrix.sub_apply]
      exact hH.eval_matrix.sub measurable_const
  exact measurable_matrix_inv_apply hM x y

private theorem gco_measurable_signedGreen (d : Dims) (N : ℕ) (t : ℝ) (z : ℂ) (σ : Bool)
    (x y : d.Idx N) :
    Measurable fun ω => RBM.signedGreen ((ouCommonFlow d).Ht N t ω) z σ x y := by
  cases σ
  · have h : ∀ ω, RBM.signedGreen ((ouCommonFlow d).Ht N t ω) z false x y =
        green ((ouCommonFlow d).Ht N t ω) (starRingEnd ℂ z) x y := fun ω => rfl
    simpa only [h] using gco_measurable_green d N t (starRingEnd ℂ z) x y
  · have h : ∀ ω, RBM.signedGreen ((ouCommonFlow d).Ht N t ω) z true x y =
        green ((ouCommonFlow d).Ht N t ω) z x y := fun ω => rfl
    simpa only [h] using gco_measurable_green d N t z x y

private theorem gco_measurable_mul_apply {ι : Type*} [Fintype ι]
    {A B : ouCommonOmega d → Matrix ι ι ℂ}
    (hA : ∀ i j, Measurable fun ω => A ω i j) (hB : ∀ i j, Measurable fun ω => B ω i j)
    (i j : ι) : Measurable fun ω => (A ω * B ω) i j := by
  simp only [Matrix.mul_apply]
  exact Finset.measurable_sum _ fun k _ => (hA i k).mul (hB k j)

private theorem gco_measurable_stieltjes (d : Dims) (N : ℕ) (t : ℝ) (z : ℂ) :
    Measurable fun ω => (RBM.stieltjes ((ouCommonFlow d).Ht N t ω) z).im := by
  have hM : Measurable fun ω => RBM.stieltjes ((ouCommonFlow d).Ht N t ω) z := by
    unfold RBM.stieltjes
    refine Measurable.const_mul ?_ _
    unfold Matrix.trace Matrix.diag
    exact Finset.measurable_sum _ fun x _ => gco_measurable_green d N t z x x
  exact Complex.measurable_im.comp hM

private theorem gco_measurable_paperK1 (d : Dims) (N : ℕ) (t : ℝ) (z : ℂ) (σ τ : Bool) :
    Measurable fun ω => RBM.paperK1Contraction N ((ouCommonFlow d).Ht N t ω) z σ τ := by
  unfold RBM.paperK1Contraction
  refine Measurable.const_mul ?_ _
  refine Finset.measurable_sum _ fun a _ => Finset.measurable_sum _ fun b _ => ?_
  exact ((gco_measurable_mul_apply
      (fun i j => gco_measurable_signedGreen d N t z σ i j)
      (fun i j => gco_measurable_signedGreen d N t z σ i j) a a).mul measurable_const).mul
    (gco_measurable_signedGreen d N t z τ b b)

private theorem gco_measurable_paperK2 (d : Dims) (N : ℕ) (t : ℝ) (z₁ z₂ : ℂ) (σ τ : Bool) :
    Measurable fun ω => RBM.paperK2Contraction N ((ouCommonFlow d).Ht N t ω) z₁ z₂ σ τ := by
  unfold RBM.paperK2Contraction
  refine Measurable.const_mul ?_ _
  refine Finset.measurable_sum _ fun a _ => Finset.measurable_sum _ fun b _ => ?_
  exact ((gco_measurable_mul_apply
      (fun i j => gco_measurable_signedGreen d N t z₁ σ i j)
      (fun i j => gco_measurable_signedGreen d N t z₁ σ i j) a b).mul measurable_const).mul
    (gco_measurable_mul_apply
      (fun i j => gco_measurable_signedGreen d N t z₂ τ i j)
      (fun i j => gco_measurable_signedGreen d N t z₂ τ i j) b a)

private theorem gco_measurable_paperL1Kernel (d : Dims) (N : ℕ) (t : ℝ) (z : ℂ) :
    Measurable fun ω => RBM.paperL1Kernel d N ((ouCommonFlow d).Ht N t ω) z := by
  unfold RBM.paperL1Kernel
  exact Finset.measurable_sum _ fun σ _ =>
    Finset.measurable_sum _ fun τ _ => (gco_measurable_paperK1 d N t z σ τ).norm

private theorem gco_measurable_paperL2Kernel (d : Dims) (N : ℕ) (t : ℝ) (z₁ z₂ : ℂ) :
    Measurable fun ω => RBM.paperL2Kernel d N ((ouCommonFlow d).Ht N t ω) z₁ z₂ := by
  unfold RBM.paperL2Kernel
  exact Finset.measurable_sum _ fun σ _ =>
    Finset.measurable_sum _ fun τ _ => (gco_measurable_paperK2 d N t z₁ z₂ σ τ).norm

private theorem gco_measurable_RHSb (d : Dims) (N : ℕ) {n : ℕ} (z : Fin n → ℂ) (t : ℝ) :
    Measurable fun ω => gco_RHSb d N z ((ouCommonFlow d).Ht N t ω) := by
  unfold gco_RHSb
  refine Measurable.add ?_ ?_
  · refine Finset.measurable_sum _ fun i _ => ?_
    exact (Finset.measurable_prod _ fun j _ => gco_measurable_stieltjes d N t (z j)).mul
      (gco_measurable_paperL1Kernel d N t (z i))
  · refine Finset.measurable_sum _ fun i _ => ?_
    refine Finset.measurable_sum _ fun j _ => ?_
    exact (Finset.measurable_prod _ fun k _ => gco_measurable_stieltjes d N t (z k)).mul
      (gco_measurable_paperL2Kernel d N t (z i) (z j))

/-- The `hB` integrand is integrable along the flow, for every `t`. -/
private theorem gco_integrable_RHSb (d : Dims) (N : ℕ) {n : ℕ} (z : Fin n → ℂ)
    (hz : ∀ i, 0 < (z i).im) (t : ℝ) :
    Integrable (fun ω => gco_RHSb d N z ((ouCommonFlow d).Ht N t ω)) (ouCommonMeasure d) := by
  obtain ⟨C, hC⟩ := gco_abs_RHSb_le d N z hz
  refine Integrable.of_bound (gco_measurable_RHSb d N z t).aestronglyMeasurable C
    (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs]
  exact hC _ ((ouCommonFlow d).hermitian N t ω)

/-! ## 5. Assembly: `eq225` -/

set_option maxHeartbeats 1000000 in
-- The `(ouCommonBand d).Idx N` / `d.Idx N` unfolding chain (both reduce to
-- `ZMod (d.L N) × Fin (d.W N)`, but only through several `def`s) makes elaboration of this
-- assembly slow; the proof itself has no `sorry` and needs no extra hypothesis.
theorem eq225 (d : Dims) (N : ℕ) {n : ℕ} (z : Fin n → ℂ) (hz : ∀ i, 0 < (z i).im)
    {T Bd : ℝ} (hT : 0 ≤ T)
    (hB : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      ∫ ω, ((∑ i, (∏ j ∈ Finset.univ.erase i,
          (RBM.stieltjes ((ouCommonFlow d).Ht N t ω) (z j)).im) *
            RBM.paperL1Kernel d N ((ouCommonFlow d).Ht N t ω) (z i)) +
        ∑ i, ∑ j ∈ Finset.univ.erase i,
          (∏ k ∈ (Finset.univ.erase i).erase j,
            (RBM.stieltjes ((ouCommonFlow d).Ht N t ω) (z k)).im) *
            RBM.paperL2Kernel d N ((ouCommonFlow d).Ht N t ω) (z i) (z j))
        ∂(ouCommonMeasure d) ≤ Bd) :
    |(∫ ω, ∏ i, (RBM.stieltjes ((ouCommonFlow d).Ht N 0 ω) (z i)).im ∂(ouCommonMeasure d)) -
      ∫ ω, ∏ i, (RBM.stieltjes ((ouCommonFlow d).Ht N T ω) (z i)).im ∂(ouCommonMeasure d)| ≤
      (1 / 2) * T * Bd := by
  classical
  set Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ :=
    fun K => ((∏ i, (RBM.stieltjes K (z i)).im : ℝ) : ℂ) with hΦdef
  have hΦ : TestFun' d N Φ := testFun'_stieltjesImProduct d N z hz
  have hcast : ∀ t : ℝ, (∫ ω, Φ ((ouCommonFlow d).Ht N t ω) ∂(ouCommonMeasure d)) =
      ((∫ ω, ∏ i, (RBM.stieltjes ((ouCommonFlow d).Ht N t ω) (z i)).im
          ∂(ouCommonMeasure d) : ℝ) : ℂ) := by
    intro t
    simp only [hΦdef]
    exact integral_ofReal
  have hftc := ouCommon_integral_sub_eq d N hΦ hT
  set g : ℝ → ℂ := fun t => (-(1 / 2 : ℝ) * Real.exp (-t)) • ∑ a : d.Idx N, ∑ b : d.Idx N,
      (RBM.centeredVarianceEntry d N a b : ℂ) *
        ∫ ω, wirtSecond d N Φ ((ouCommonFlow d).Ht N t ω) a b ∂(ouCommonMeasure d) with hgdef
  have key : ((∫ ω, ∏ i, (RBM.stieltjes ((ouCommonFlow d).Ht N T ω) (z i)).im
        ∂(ouCommonMeasure d) : ℝ) : ℂ) -
      ((∫ ω, ∏ i, (RBM.stieltjes ((ouCommonFlow d).Ht N 0 ω) (z i)).im
        ∂(ouCommonMeasure d) : ℝ) : ℂ) = ∫ t in (0:ℝ)..T, g t := by
    rw [← hcast T, ← hcast 0]
    exact hftc
  have hTne : ∀ᵐ t : ℝ, t ≠ T := MeasureTheory.volume.ae_ne T
  have hnormg : ∀ᵐ t : ℝ, t ∈ Set.Ioc (0 : ℝ) T → ‖g t‖ ≤ (1 / 2) * Bd := by
    filter_upwards [hTne] with t htne hmem
    have ht0 : t ∈ Set.Ioo (0 : ℝ) T := ⟨hmem.1, hmem.2.lt_of_ne htne⟩
    have hS : ‖∑ a : d.Idx N, ∑ b : d.Idx N, (RBM.centeredVarianceEntry d N a b : ℂ) *
        ∫ ω, wirtSecond d N Φ ((ouCommonFlow d).Ht N t ω) a b ∂(ouCommonMeasure d)‖ ≤ Bd := by
      rw [gco_sum_integral_swap hΦ t]
      refine (norm_integral_le_integral_norm _).trans ?_
      have hbound : ∀ᵐ ω ∂(ouCommonMeasure d),
          ‖∑ a : d.Idx N, ∑ b : d.Idx N, (RBM.centeredVarianceEntry d N a b : ℂ) *
              wirtSecond d N Φ ((ouCommonFlow d).Ht N t ω) a b‖ ≤ gco_RHSb d N z
                ((ouCommonFlow d).Ht N t ω) := by
        refine Eventually.of_forall fun ω => ?_
        have hpt := centeredVariance_wirtProduct_kernel_bound (d := d) (N := N)
          (s := (Finset.univ : Finset (Fin n)))
          (H := (ouCommonFlow d).Ht N t ω) ((ouCommonFlow d).hermitian N t ω) z
          (fun i _ => hz i)
        rw [← hΦdef] at hpt
        simpa [gco_RHSb] using hpt
      refine (MeasureTheory.integral_mono_of_nonneg (Eventually.of_forall fun ω => norm_nonneg _)
        (gco_integrable_RHSb d N z hz t) hbound).trans ?_
      exact hB t ht0
    calc ‖g t‖ = ‖(-(1 / 2 : ℝ) * Real.exp (-t))‖ *
        ‖∑ a : d.Idx N, ∑ b : d.Idx N, (RBM.centeredVarianceEntry d N a b : ℂ) *
            ∫ ω, wirtSecond d N Φ ((ouCommonFlow d).Ht N t ω) a b ∂(ouCommonMeasure d)‖ := by
          rw [hgdef, norm_smul, Real.norm_eq_abs]
      _ ≤ (1 / 2 : ℝ) * Bd := by
          have hexp : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [ht0.1])
          have hexppos : 0 < Real.exp (-t) := Real.exp_pos _
          have habs : ‖(-(1 / 2 : ℝ) * Real.exp (-t))‖ = (1 / 2 : ℝ) * Real.exp (-t) := by
            rw [Real.norm_eq_abs, abs_of_neg (by nlinarith [hexppos])]
            ring
          rw [habs]
          have hSnn : (0:ℝ) ≤ ‖∑ a : d.Idx N, ∑ b : d.Idx N,
              (RBM.centeredVarianceEntry d N a b : ℂ) *
                ∫ ω, wirtSecond d N Φ ((ouCommonFlow d).Ht N t ω) a b
                  ∂(ouCommonMeasure d)‖ := norm_nonneg _
          nlinarith [mul_le_mul_of_nonneg_right hexp hSnn, hS]
  have hnormInt : ‖∫ t in (0:ℝ)..T, g t‖ ≤ (1 / 2 : ℝ) * Bd * |T - 0| := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const_ae
      (a := (0:ℝ)) (b := T) (f := g) (C := (1 / 2 : ℝ) * Bd) ?_
    · simpa using this
    · rw [Set.uIoc_of_le hT]
      exact hnormg
  rw [abs_sub_comm]
  calc |(∫ ω, ∏ i, (RBM.stieltjes ((ouCommonFlow d).Ht N T ω) (z i)).im ∂(ouCommonMeasure d)) -
        ∫ ω, ∏ i, (RBM.stieltjes ((ouCommonFlow d).Ht N 0 ω) (z i)).im ∂(ouCommonMeasure d)|
      = ‖((∫ ω, ∏ i, (RBM.stieltjes ((ouCommonFlow d).Ht N T ω) (z i)).im
            ∂(ouCommonMeasure d) : ℝ) : ℂ) -
          ((∫ ω, ∏ i, (RBM.stieltjes ((ouCommonFlow d).Ht N 0 ω) (z i)).im
            ∂(ouCommonMeasure d) : ℝ) : ℂ)‖ := by
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    _ = ‖∫ t in (0:ℝ)..T, g t‖ := by rw [key]
    _ ≤ (1 / 2 : ℝ) * Bd * |T - 0| := hnormInt
    _ = (1 / 2) * T * Bd := by rw [sub_zero, abs_of_nonneg hT]; ring

end RBM.Gauss
