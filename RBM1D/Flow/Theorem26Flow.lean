/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Flow.GreenCorrComparison
import RBM1D.Flow.GreenComparisonOU
import RBM1D.Flow.Step3KernelBounds
import RBM1D.Flow.Step3KernelBoundsL2
import RBM1D.Flow.DBMInput
import RBM1D.Flow.EigenMeasurable

/-!
# Theorem 2.6, Steps 2–3: the terminal assembly on the common OU carrier

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, Theorem 2.6, Steps 2–3.

* `claim223_of_flow`: Step 3, (2.25) + the per-time kernel bounds ⇒ (2.23) at
  `c' = c/36`, `C = 24`, for `0 < τ_U < c/3`, conditional on the single-scale local law
  `FlowLocalLaw` ((2.26)) and on `FlowEq747` ((7.47)).
* `aprioriImM_of_flowLocalLaw`: the a priori input `E (Im m_0(E+i/N))^n ≤ N^ε` of the internal
  (2.23) ⇒ (2.24), from `FlowLocalLaw` at `t = 0` (monotonicity in `η` and Jensen).
* `step2Output_of_flow`: **(2.24) in the interface**, `Step2Output d κ`, with an explicit
  `τ_U ∈ (0,1)`; the law transfer from the common carrier to `P d` / `ouProductMeasure d N` is
  `corrPairing_congr_law` twice.

`FlowLocalLaw` and `FlowEq747` are hypotheses here (they are produced in
`Flow/FlowRandomLayer.lean`, §7.2).
-/

namespace RBM.Gauss

open MeasureTheory Filter Matrix Topology
open scoped ComplexConjugate Matrix.Norms.L2Operator

/-! ### Measurability and crude bounds along the carrier flow (file-local helpers) -/

private theorem Theorem26Flow.measurable_green (d : Dims) (N : ℕ) (t : ℝ) (z : ℂ)
    (x y : d.Idx N) :
    Measurable fun ω => green ((ouCommonFlow d).Ht N t ω) z x y := by
  have hH := ouCommonFlow_measurable d N t
  have hM : Measurable fun ω => (ouCommonFlow d).Ht N t ω - z • (1 : Matrix _ _ ℂ) :=
    Measurable.of_eval_matrix _ fun a b => by
      simp only [Matrix.sub_apply]
      exact hH.eval_matrix.sub measurable_const
  exact measurable_matrix_inv_apply hM x y

private theorem Theorem26Flow.measurable_signedGreen (d : Dims) (N : ℕ) (t : ℝ) (z : ℂ)
    (σ : Bool) (x y : d.Idx N) :
    Measurable fun ω => RBM.signedGreen ((ouCommonFlow d).Ht N t ω) z σ x y := by
  cases σ
  · have h : ∀ ω, RBM.signedGreen ((ouCommonFlow d).Ht N t ω) z false x y =
        green ((ouCommonFlow d).Ht N t ω) (starRingEnd ℂ z) x y := fun ω => rfl
    simpa only [h] using Theorem26Flow.measurable_green d N t (starRingEnd ℂ z) x y
  · have h : ∀ ω, RBM.signedGreen ((ouCommonFlow d).Ht N t ω) z true x y =
        green ((ouCommonFlow d).Ht N t ω) z x y := fun ω => rfl
    simpa only [h] using Theorem26Flow.measurable_green d N t z x y

private theorem Theorem26Flow.measurable_mul_apply {d : Dims} {ι : Type*} [Fintype ι]
    {A B : ouCommonOmega d → Matrix ι ι ℂ}
    (hA : ∀ i j, Measurable fun ω => A ω i j) (hB : ∀ i j, Measurable fun ω => B ω i j)
    (i j : ι) : Measurable fun ω => (A ω * B ω) i j := by
  simp only [Matrix.mul_apply]
  exact Finset.measurable_sum _ fun k _ => (hA i k).mul (hB k j)

private theorem Theorem26Flow.measurable_stieltjes_im (d : Dims) (N : ℕ) (t : ℝ) (z : ℂ) :
    Measurable fun ω => (RBM.stieltjes ((ouCommonFlow d).Ht N t ω) z).im := by
  have hM : Measurable fun ω => RBM.stieltjes ((ouCommonFlow d).Ht N t ω) z := by
    unfold RBM.stieltjes
    refine Measurable.const_mul ?_ _
    unfold Matrix.trace Matrix.diag
    exact Finset.measurable_sum _ fun x _ => Theorem26Flow.measurable_green d N t z x x
  exact Complex.measurable_im.comp hM

private theorem Theorem26Flow.measurable_paperL1Kernel (d : Dims) (N : ℕ) (t : ℝ) (z : ℂ) :
    Measurable fun ω => RBM.paperL1Kernel d N ((ouCommonFlow d).Ht N t ω) z := by
  unfold RBM.paperL1Kernel
  refine Finset.measurable_sum _ fun σ _ => Finset.measurable_sum _ fun τ _ => ?_
  refine Measurable.norm ?_
  refine Measurable.const_mul ?_ _
  refine Finset.measurable_sum _ fun a _ => Finset.measurable_sum _ fun b _ => ?_
  exact ((Theorem26Flow.measurable_mul_apply
      (fun i j => Theorem26Flow.measurable_signedGreen d N t z σ i j)
      (fun i j => Theorem26Flow.measurable_signedGreen d N t z σ i j) a a).mul
      measurable_const).mul
    (Theorem26Flow.measurable_signedGreen d N t z τ b b)

private theorem Theorem26Flow.measurable_paperL2Kernel (d : Dims) (N : ℕ) (t : ℝ)
    (z₁ z₂ : ℂ) :
    Measurable fun ω => RBM.paperL2Kernel d N ((ouCommonFlow d).Ht N t ω) z₁ z₂ := by
  unfold RBM.paperL2Kernel
  refine Finset.measurable_sum _ fun σ _ => Finset.measurable_sum _ fun τ _ => ?_
  refine Measurable.norm ?_
  refine Measurable.const_mul ?_ _
  refine Finset.measurable_sum _ fun a _ => Finset.measurable_sum _ fun b _ => ?_
  exact ((Theorem26Flow.measurable_mul_apply
      (fun i j => Theorem26Flow.measurable_signedGreen d N t z₁ σ i j)
      (fun i j => Theorem26Flow.measurable_signedGreen d N t z₁ σ i j) a b).mul
      measurable_const).mul
    (Theorem26Flow.measurable_mul_apply
      (fun i j => Theorem26Flow.measurable_signedGreen d N t z₂ τ i j)
      (fun i j => Theorem26Flow.measurable_signedGreen d N t z₂ τ i j) b a)

private theorem Theorem26Flow.norm_signedGreen_le {ι : Type*} [Fintype ι] [DecidableEq ι]
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

private theorem Theorem26Flow.norm_centeredVarianceEntry_le (d : Dims) (N : ℕ)
    (a b : d.Idx N) : ‖(RBM.centeredVarianceEntry d N a b : ℂ)‖ ≤ 2 := by
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

private theorem Theorem26Flow.norm_card_inv_le (d : Dims) (N : ℕ) :
    ‖((Fintype.card (d.Idx N) : ℂ)⁻¹)‖ ≤ 1 := by
  rw [norm_inv, Complex.norm_natCast]
  rcases Nat.eq_zero_or_pos (Fintype.card (d.Idx N)) with h0 | hpos
  · simp [h0]
  · exact inv_le_one_of_one_le₀ (by exact_mod_cast hpos)

/-- Crude bound on the `L₁` kernel, uniform over Hermitian `H`. -/
private theorem Theorem26Flow.paperL1Kernel_le {d : Dims} {N : ℕ}
    {H : Matrix (d.Idx N) (d.Idx N) ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : 0 < z.im) :
    RBM.paperL1Kernel d N H z ≤ 8 * (Fintype.card (d.Idx N) : ℝ) ^ 2 * z.im⁻¹ ^ 3 := by
  have hterm : ∀ σ τ : Bool, ∀ a b : d.Idx N,
      ‖(RBM.signedGreen H z σ * RBM.signedGreen H z σ) a a *
        (RBM.centeredVarianceEntry d N a b : ℂ) * RBM.signedGreen H z τ b b‖ ≤
      2 * z.im⁻¹ ^ 3 := by
    intro σ τ a b
    have h1 : ‖(RBM.signedGreen H z σ * RBM.signedGreen H z σ) a a‖ ≤ z.im⁻¹ * z.im⁻¹ := by
      refine (RBM.norm_apply_le_l2_opNorm _ a a).trans ?_
      refine (norm_mul_le _ _).trans ?_
      exact mul_le_mul (Theorem26Flow.norm_signedGreen_le hH hz σ)
        (Theorem26Flow.norm_signedGreen_le hH hz σ) (norm_nonneg _) (by positivity)
    have h2 := Theorem26Flow.norm_centeredVarianceEntry_le d N a b
    have h3 : ‖RBM.signedGreen H z τ b b‖ ≤ z.im⁻¹ :=
      (RBM.norm_apply_le_l2_opNorm _ b b).trans (Theorem26Flow.norm_signedGreen_le hH hz τ)
    rw [norm_mul, norm_mul]
    calc _ ≤ (z.im⁻¹ * z.im⁻¹) * 2 * z.im⁻¹ := by gcongr
      _ = 2 * z.im⁻¹ ^ 3 := by ring
  have hK : ∀ σ τ : Bool,
      ‖(Fintype.card (d.Idx N) : ℂ)⁻¹ * ∑ a : d.Idx N, ∑ b : d.Idx N,
        (RBM.signedGreen H z σ * RBM.signedGreen H z σ) a a *
          (RBM.centeredVarianceEntry d N a b : ℂ) * RBM.signedGreen H z τ b b‖ ≤
        (Fintype.card (d.Idx N) : ℝ) ^ 2 * (2 * z.im⁻¹ ^ 3) := by
    intro σ τ
    rw [norm_mul]
    have hsum : ‖∑ a : d.Idx N, ∑ b : d.Idx N,
        (RBM.signedGreen H z σ * RBM.signedGreen H z σ) a a *
          (RBM.centeredVarianceEntry d N a b : ℂ) * RBM.signedGreen H z τ b b‖ ≤
        (Fintype.card (d.Idx N) : ℝ) ^ 2 * (2 * z.im⁻¹ ^ 3) := by
      refine (norm_sum_le _ _).trans ?_
      refine (Finset.sum_le_sum fun a _ => norm_sum_le _ _).trans ?_
      refine (Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ =>
        hterm σ τ a b).trans ?_
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      ring_nf
      exact le_rfl
    calc _ ≤ 1 * ((Fintype.card (d.Idx N) : ℝ) ^ 2 * (2 * z.im⁻¹ ^ 3)) := by
          gcongr
          exact Theorem26Flow.norm_card_inv_le d N
      _ = _ := one_mul _
  unfold RBM.paperL1Kernel
  calc _ ≤ ∑ _σ : Bool, ∑ _τ : Bool,
        (Fintype.card (d.Idx N) : ℝ) ^ 2 * (2 * z.im⁻¹ ^ 3) :=
        Finset.sum_le_sum fun σ _ => Finset.sum_le_sum fun τ _ => hK σ τ
    _ = 8 * (Fintype.card (d.Idx N) : ℝ) ^ 2 * z.im⁻¹ ^ 3 := by
        simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_bool]
        ring

/-- Crude bound on the `L₂` kernel, uniform over Hermitian `H`. -/
private theorem Theorem26Flow.paperL2Kernel_le {d : Dims} {N : ℕ}
    {H : Matrix (d.Idx N) (d.Idx N) ℂ} (hH : H.IsHermitian) {z₁ z₂ : ℂ} (hz₁ : 0 < z₁.im)
    (hz₂ : 0 < z₂.im) :
    RBM.paperL2Kernel d N H z₁ z₂ ≤
      8 * (Fintype.card (d.Idx N) : ℝ) ^ 2 * (z₁.im⁻¹ ^ 2 * z₂.im⁻¹ ^ 2) := by
  have hterm : ∀ σ τ : Bool, ∀ a b : d.Idx N,
      ‖(RBM.signedGreen H z₁ σ * RBM.signedGreen H z₁ σ) a b *
        (RBM.centeredVarianceEntry d N a b : ℂ) *
          (RBM.signedGreen H z₂ τ * RBM.signedGreen H z₂ τ) b a‖ ≤
      2 * (z₁.im⁻¹ ^ 2 * z₂.im⁻¹ ^ 2) := by
    intro σ τ a b
    have h1 : ‖(RBM.signedGreen H z₁ σ * RBM.signedGreen H z₁ σ) a b‖ ≤
        z₁.im⁻¹ * z₁.im⁻¹ := by
      refine (RBM.norm_apply_le_l2_opNorm _ a b).trans ?_
      refine (norm_mul_le _ _).trans ?_
      exact mul_le_mul (Theorem26Flow.norm_signedGreen_le hH hz₁ σ)
        (Theorem26Flow.norm_signedGreen_le hH hz₁ σ) (norm_nonneg _) (by positivity)
    have h2 := Theorem26Flow.norm_centeredVarianceEntry_le d N a b
    have h3 : ‖(RBM.signedGreen H z₂ τ * RBM.signedGreen H z₂ τ) b a‖ ≤
        z₂.im⁻¹ * z₂.im⁻¹ := by
      refine (RBM.norm_apply_le_l2_opNorm _ b a).trans ?_
      refine (norm_mul_le _ _).trans ?_
      exact mul_le_mul (Theorem26Flow.norm_signedGreen_le hH hz₂ τ)
        (Theorem26Flow.norm_signedGreen_le hH hz₂ τ) (norm_nonneg _) (by positivity)
    rw [norm_mul, norm_mul]
    calc _ ≤ (z₁.im⁻¹ * z₁.im⁻¹) * 2 * (z₂.im⁻¹ * z₂.im⁻¹) := by gcongr
      _ = 2 * (z₁.im⁻¹ ^ 2 * z₂.im⁻¹ ^ 2) := by ring
  have hK : ∀ σ τ : Bool,
      ‖(Fintype.card (d.Idx N) : ℂ)⁻¹ * (Fintype.card (d.Idx N) : ℂ)⁻¹ *
        ∑ a : d.Idx N, ∑ b : d.Idx N,
          (RBM.signedGreen H z₁ σ * RBM.signedGreen H z₁ σ) a b *
            (RBM.centeredVarianceEntry d N a b : ℂ) *
            (RBM.signedGreen H z₂ τ * RBM.signedGreen H z₂ τ) b a‖ ≤
        (Fintype.card (d.Idx N) : ℝ) ^ 2 * (2 * (z₁.im⁻¹ ^ 2 * z₂.im⁻¹ ^ 2)) := by
    intro σ τ
    rw [norm_mul, norm_mul]
    have hsum : ‖∑ a : d.Idx N, ∑ b : d.Idx N,
        (RBM.signedGreen H z₁ σ * RBM.signedGreen H z₁ σ) a b *
          (RBM.centeredVarianceEntry d N a b : ℂ) *
          (RBM.signedGreen H z₂ τ * RBM.signedGreen H z₂ τ) b a‖ ≤
        (Fintype.card (d.Idx N) : ℝ) ^ 2 * (2 * (z₁.im⁻¹ ^ 2 * z₂.im⁻¹ ^ 2)) := by
      refine (norm_sum_le _ _).trans ?_
      refine (Finset.sum_le_sum fun a _ => norm_sum_le _ _).trans ?_
      refine (Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ =>
        hterm σ τ a b).trans ?_
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      ring_nf
      exact le_rfl
    have hc := Theorem26Flow.norm_card_inv_le d N
    calc _ ≤ 1 * 1 * ((Fintype.card (d.Idx N) : ℝ) ^ 2 *
          (2 * (z₁.im⁻¹ ^ 2 * z₂.im⁻¹ ^ 2))) := by
          gcongr
      _ = _ := by ring
  unfold RBM.paperL2Kernel
  calc _ ≤ ∑ _σ : Bool, ∑ _τ : Bool,
        (Fintype.card (d.Idx N) : ℝ) ^ 2 * (2 * (z₁.im⁻¹ ^ 2 * z₂.im⁻¹ ^ 2)) :=
        Finset.sum_le_sum fun σ _ => Finset.sum_le_sum fun τ _ => hK σ τ
    _ = 8 * (Fintype.card (d.Idx N) : ℝ) ^ 2 * (z₁.im⁻¹ ^ 2 * z₂.im⁻¹ ^ 2) := by
        simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_bool]
        ring

private theorem Theorem26Flow.paperL1Kernel_nonneg (d : Dims) (N : ℕ)
    (H : Matrix (d.Idx N) (d.Idx N) ℂ) (z : ℂ) : 0 ≤ RBM.paperL1Kernel d N H z := by
  unfold RBM.paperL1Kernel
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

private theorem Theorem26Flow.paperL2Kernel_nonneg (d : Dims) (N : ℕ)
    (H : Matrix (d.Idx N) (d.Idx N) ℂ) (z₁ z₂ : ℂ) : 0 ≤ RBM.paperL2Kernel d N H z₁ z₂ := by
  unfold RBM.paperL2Kernel
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

private theorem Theorem26Flow.abs_stieltjes_im_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : 0 < z.im) :
    |(RBM.stieltjes H z).im| ≤ (Fintype.card ι : ℝ) * z.im⁻¹ := by
  refine (Complex.abs_im_le_norm _).trans ?_
  have hcardnorm : ‖((Fintype.card ι : ℂ)⁻¹)‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_natCast]
    rcases Nat.eq_zero_or_pos (Fintype.card ι) with h0 | hpos
    · simp [h0]
    · exact inv_le_one_of_one_le₀ (by exact_mod_cast hpos)
  have htrace : ‖(green H z).trace‖ ≤ (Fintype.card ι : ℝ) * z.im⁻¹ := by
    unfold Matrix.trace Matrix.diag
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i : ι, ‖green H z i i‖ ≤ ∑ _i : ι, z.im⁻¹ :=
          Finset.sum_le_sum fun i _ =>
            (RBM.norm_apply_le_l2_opNorm _ i i).trans (norm_green_le hH hz (le_abs_self z.im))
      _ = (Fintype.card ι : ℝ) * z.im⁻¹ := by
          rw [Finset.sum_const, Finset.card_univ]; ring
  unfold RBM.stieltjes
  rw [norm_mul]
  calc _ ≤ 1 * ((Fintype.card ι : ℝ) * z.im⁻¹) := by gcongr
    _ = _ := one_mul _

private theorem Theorem26Flow.abs_prod_stieltjes_im_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {m : ℕ} (s : Finset (Fin m)) (w : Fin m → ℂ)
    (hw : ∀ j, 0 < (w j).im) :
    |∏ j ∈ s, (RBM.stieltjes H (w j)).im| ≤ ∏ j ∈ s, ((Fintype.card ι : ℝ) * (w j).im⁻¹) := by
  rw [Finset.abs_prod]
  exact Finset.prod_le_prod₀ (fun j _ => abs_nonneg _)
    (fun j _ => Theorem26Flow.abs_stieltjes_im_le hH (hw j))

private theorem Theorem26Flow.integrable_L1 (d : Dims) (N : ℕ) (t : ℝ) {m : ℕ}
    (s : Finset (Fin m)) (w : Fin m → ℂ) (u : ℂ) (hw : ∀ j, 0 < (w j).im) (hu : 0 < u.im) :
    Integrable (fun ω => (∏ j ∈ s, (RBM.stieltjes ((ouCommonFlow d).Ht N t ω) (w j)).im) *
      RBM.paperL1Kernel d N ((ouCommonFlow d).Ht N t ω) u) (ouCommonMeasure d) := by
  refine Integrable.of_bound
    ((Finset.measurable_prod _ fun j _ =>
      Theorem26Flow.measurable_stieltjes_im d N t (w j)).mul
      (Theorem26Flow.measurable_paperL1Kernel d N t u)).aestronglyMeasurable
    ((∏ j ∈ s, ((Fintype.card (d.Idx N) : ℝ) * (w j).im⁻¹)) *
      (8 * (Fintype.card (d.Idx N) : ℝ) ^ 2 * u.im⁻¹ ^ 3)) (Eventually.of_forall fun ω => ?_)
  have hH := (ouCommonFlow d).hermitian N t ω
  have hnn : 0 ≤ RBM.paperL1Kernel d N ((ouCommonFlow d).Ht N t ω) u :=
    Theorem26Flow.paperL1Kernel_nonneg d N _ u
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hnn]
  exact mul_le_mul (Theorem26Flow.abs_prod_stieltjes_im_le hH s w hw)
    (Theorem26Flow.paperL1Kernel_le hH hu) hnn
    ((abs_nonneg _).trans (Theorem26Flow.abs_prod_stieltjes_im_le hH s w hw))

private theorem Theorem26Flow.integrable_L2 (d : Dims) (N : ℕ) (t : ℝ) {m : ℕ}
    (s : Finset (Fin m)) (w : Fin m → ℂ) (u₁ u₂ : ℂ) (hw : ∀ j, 0 < (w j).im)
    (hu₁ : 0 < u₁.im) (hu₂ : 0 < u₂.im) :
    Integrable (fun ω => (∏ j ∈ s, (RBM.stieltjes ((ouCommonFlow d).Ht N t ω) (w j)).im) *
      RBM.paperL2Kernel d N ((ouCommonFlow d).Ht N t ω) u₁ u₂) (ouCommonMeasure d) := by
  refine Integrable.of_bound
    ((Finset.measurable_prod _ fun j _ =>
      Theorem26Flow.measurable_stieltjes_im d N t (w j)).mul
      (Theorem26Flow.measurable_paperL2Kernel d N t u₁ u₂)).aestronglyMeasurable
    ((∏ j ∈ s, ((Fintype.card (d.Idx N) : ℝ) * (w j).im⁻¹)) *
      (8 * (Fintype.card (d.Idx N) : ℝ) ^ 2 * (u₁.im⁻¹ ^ 2 * u₂.im⁻¹ ^ 2)))
    (Eventually.of_forall fun ω => ?_)
  have hH := (ouCommonFlow d).hermitian N t ω
  have hnn : 0 ≤ RBM.paperL2Kernel d N ((ouCommonFlow d).Ht N t ω) u₁ u₂ :=
    Theorem26Flow.paperL2Kernel_nonneg d N _ u₁ u₂
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hnn]
  exact mul_le_mul (Theorem26Flow.abs_prod_stieltjes_im_le hH s w hw)
    (Theorem26Flow.paperL2Kernel_le hH hu₁ hu₂) hnn
    ((abs_nonneg _).trans (Theorem26Flow.abs_prod_stieltjes_im_le hH s w hw))

private theorem Theorem26Flow.tendsto_rpow (d : Dims) {e : ℝ} (he : e < 0) :
    Tendsto (fun N => ((ouCommonBand d).size N : ℝ) ^ e) atTop (𝓝 0) := by
  have h := (tendsto_rpow_neg_atTop (y := -e) (by linarith)).comp
    ((tendsto_natCast_atTop_atTop (R := ℝ)).comp (ouCommonBand d).tendsto_size)
  refine h.congr fun N => ?_
  simp [Function.comp]

private theorem Theorem26Flow.one_le_size (d : Dims) (N : ℕ) :
    (1 : ℝ) ≤ ((ouCommonBand d).size N : ℝ) := by
  exact_mod_cast (ouCommonBand d).one_le_size N

private theorem Theorem26Flow.card_idx (d : Dims) (N : ℕ) :
    (Fintype.card (d.Idx N) : ℝ) = ((ouCommonBand d).size N : ℝ) := by
  have h : Fintype.card (d.Idx N) = (ouCommonBand d).size N := by
    simp [Band.size, ouCommonBand, Dims.Idx, ZMod.card]
  exact_mod_cast h

/-! ### (2.23) from (2.25) and the per-time kernel bounds -/

/-- **(2.23) on the common OU carrier** (Theorem 2.6, Step 3), with `c' = c/36`, `C = 24`:
from (2.25) (`eq225`) and the per-time kernel bounds `expect_L1_weighted_le`,
`expect_L2_weighted_le`, conditional on the single-scale local law (2.26) and on (7.47). -/
theorem claim223_of_flow (d : Dims) {κ τU : ℝ} (hκ : 0 < κ) (hτU : 0 < τU)
    (hτc : τU < d.c / 3) (hLL : FlowLocalLaw d κ τU) (hQUE : FlowEq747 d κ τU)
    (E : ℝ) (hE : |E| ≤ 2 - κ) (n : ℕ) :
    Claim223 (ouCommonFlow d) E n τU (d.c / 36) 24 := by
  intro C₀ hC₀
  have hsize : Tendsto (fun N => ((ouCommonBand d).size N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (ouCommonBand d).tendsto_size
  have ev1 := expect_L1_weighted_le d hκ hτU hτc hLL hQUE E hE hC₀ n
  have ev2 := expect_L2_weighted_le d hκ hτU hτc hLL hQUE E hE hC₀ n
  have ev3 : ∀ᶠ N : ℕ in atTop, (n : ℝ) ^ 2 / 2 ≤ ((ouCommonBand d).size N : ℝ) ^ (7 * τU) :=
    ((tendsto_rpow_atTop (by positivity)).comp hsize).eventually_ge_atTop _
  filter_upwards [ev1, ev2, ev3] with N hN1 hN2 hN3
  intro z hz
  set X : ℝ := ((ouCommonBand d).size N : ℝ) with hXdef
  have hX1 : 1 ≤ X := Theorem26Flow.one_le_size d N
  have hX0 : 0 < X := by linarith
  have hzim : ∀ i, 0 < (z i).im := fun i =>
    lt_of_lt_of_le (Real.rpow_pos_of_pos hX0 _) (hz i).2.1
  have hw : ∀ i, InWindow222 d E C₀ τU N (z i) := fun i => hz i
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · subst hn0
    simp only [Finset.univ_eq_empty, Finset.prod_empty, integral_const,
      smul_eq_mul, mul_one, sub_self, abs_zero]
    exact (Real.rpow_pos_of_pos hX0 _).le
  set T : ℝ := (ouCommonBand d).tPow τU N with hTdef
  have hT0 : 0 ≤ T := (Real.rpow_pos_of_pos hX0 _).le
  set Y : ℝ := X ^ (1 - d.c / 36 + (3 * (n : ℝ) + 13) * τU) with hYdef
  have hY0 : 0 ≤ Y := (Real.rpow_pos_of_pos hX0 _).le
  -- exponent monotonicity for the weighted bounds
  have hexp : ∀ s : Finset (Fin n), s.card ≤ n - 1 →
      X ^ (1 - d.c / 36 + (3 * (s.card : ℝ) + 16) * τU) ≤ Y := by
    intro s hs
    refine Real.rpow_le_rpow_of_exponent_le hX1 ?_
    have hs' : (s.card : ℝ) + 1 ≤ n := by
      have : s.card + 1 ≤ n := by omega
      exact_mod_cast this
    nlinarith
  have hcard1 : ∀ i : Fin n, (Finset.univ.erase i).card ≤ n - 1 := fun i => by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
  have hcard2 : ∀ i j : Fin n, ((Finset.univ.erase i).erase j).card ≤ n - 1 := fun i j =>
    (Finset.card_le_card (Finset.erase_subset _ _)).trans (hcard1 i)
  have hB : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      ∫ ω, ((∑ i, (∏ j ∈ Finset.univ.erase i,
          (RBM.stieltjes ((ouCommonFlow d).Ht N t ω) (z j)).im) *
            RBM.paperL1Kernel d N ((ouCommonFlow d).Ht N t ω) (z i)) +
        ∑ i, ∑ j ∈ Finset.univ.erase i,
          (∏ k ∈ (Finset.univ.erase i).erase j,
            (RBM.stieltjes ((ouCommonFlow d).Ht N t ω) (z k)).im) *
            RBM.paperL2Kernel d N ((ouCommonFlow d).Ht N t ω) (z i) (z j))
        ∂(ouCommonMeasure d) ≤ (n : ℝ) ^ 2 * Y := by
    intro t ht
    have ht' : t ∈ Set.Ioc (0 : ℝ) ((ouCommonBand d).tPow τU N) := ⟨ht.1, ht.2.le⟩
    have hI1 : ∀ i : Fin n, Integrable (fun ω =>
        (∏ j ∈ Finset.univ.erase i, (RBM.stieltjes ((ouCommonFlow d).Ht N t ω) (z j)).im) *
          RBM.paperL1Kernel d N ((ouCommonFlow d).Ht N t ω) (z i)) (ouCommonMeasure d) :=
      fun i => Theorem26Flow.integrable_L1 d N t _ z (z i) hzim (hzim i)
    have hI2 : ∀ i j : Fin n, Integrable (fun ω =>
        (∏ k ∈ (Finset.univ.erase i).erase j,
          (RBM.stieltjes ((ouCommonFlow d).Ht N t ω) (z k)).im) *
          RBM.paperL2Kernel d N ((ouCommonFlow d).Ht N t ω) (z i) (z j)) (ouCommonMeasure d) :=
      fun i j => Theorem26Flow.integrable_L2 d N t _ z (z i) (z j) hzim (hzim i) (hzim j)
    rw [integral_add (integrable_finsetSum _ fun i _ => hI1 i)
        (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hI2 i j),
      integral_finsetSum _ fun i _ => hI1 i,
      integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hI2 i j]
    simp_rw [integral_finsetSum _ fun j _ => hI2 _ j]
    have hS1 : ∑ i : Fin n, ∫ ω,
        (∏ j ∈ Finset.univ.erase i, (RBM.stieltjes ((ouCommonFlow d).Ht N t ω) (z j)).im) *
          RBM.paperL1Kernel d N ((ouCommonFlow d).Ht N t ω) (z i) ∂(ouCommonMeasure d) ≤
        (n : ℝ) * Y := by
      calc _ ≤ ∑ _i : Fin n, Y := Finset.sum_le_sum fun i _ =>
            (hN1 t ht' _ z (z i) hw (hw i)).trans (hexp _ (hcard1 i))
        _ = (n : ℝ) * Y := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hS2 : ∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, ∫ ω,
        (∏ k ∈ (Finset.univ.erase i).erase j,
          (RBM.stieltjes ((ouCommonFlow d).Ht N t ω) (z k)).im) *
          RBM.paperL2Kernel d N ((ouCommonFlow d).Ht N t ω) (z i) (z j) ∂(ouCommonMeasure d) ≤
        (n : ℝ) * (((n : ℝ) - 1) * Y) := by
      calc _ ≤ ∑ i : Fin n, ∑ _j ∈ Finset.univ.erase i, Y :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
              (hN2 t ht' _ z (z i) (z j) hw (hw i) (hw j)).trans (hexp _ (hcard2 i j))
        _ = ∑ _i : Fin n, ((n : ℝ) - 1) * Y := Finset.sum_congr rfl fun i _ => by
            rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
              Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub hn, Nat.cast_one]
        _ = (n : ℝ) * (((n : ℝ) - 1) * Y) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    nlinarith [hS1, hS2]
  have key := eq225 d N z hzim hT0 hB
  change |(∫ ω, ∏ i, (RBM.stieltjes ((ouCommonFlow d).Ht N 0 ω) (z i)).im
      ∂(ouCommonMeasure d)) - ∫ ω, ∏ i, (RBM.stieltjes ((ouCommonFlow d).Ht N T ω) (z i)).im
      ∂(ouCommonMeasure d)| ≤ X ^ (-(d.c / 36) + 24 * (n : ℝ) * τU)
  refine key.trans ?_
  -- `½ t_U n² N^{1-c/36+(3n+13)τ} = (n²/2) N^{-c/36+(3n+14)τ} ≤ N^{-c/36+24nτ}`
  have hTY : T * Y = X ^ (-(d.c / 36) + (3 * (n : ℝ) + 14) * τU) := by
    rw [hTdef, hYdef, Band.tPow, ← hXdef, ← Real.rpow_add hX0]
    ring_nf
  have hsplit : X ^ (-(d.c / 36) + 24 * (n : ℝ) * τU) =
      X ^ (-(d.c / 36) + (3 * (n : ℝ) + 14) * τU) * X ^ ((21 * (n : ℝ) - 14) * τU) := by
    rw [← Real.rpow_add hX0]; ring_nf
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h7 : X ^ (7 * τU) ≤ X ^ ((21 * (n : ℝ) - 14) * τU) :=
    Real.rpow_le_rpow_of_exponent_le hX1 (by nlinarith)
  have hA0 : 0 ≤ X ^ (-(d.c / 36) + (3 * (n : ℝ) + 14) * τU) :=
    (Real.rpow_pos_of_pos hX0 _).le
  rw [hsplit]
  calc 1 / 2 * T * ((n : ℝ) ^ 2 * Y) = (n : ℝ) ^ 2 / 2 * (T * Y) := by ring
    _ = X ^ (-(d.c / 36) + (3 * (n : ℝ) + 14) * τU) * ((n : ℝ) ^ 2 / 2) := by rw [hTY]; ring
    _ ≤ X ^ (-(d.c / 36) + (3 * (n : ℝ) + 14) * τU) * X ^ ((21 * (n : ℝ) - 14) * τU) :=
        mul_le_mul_of_nonneg_left (hN3.trans h7) hA0

/-! ### The a priori bound at the level spacing -/

/-- Pointwise chain for the a priori bound: `η`-monotonicity, `Im m ≤ N⁻¹ ∑ |G_xx|`, Jensen,
and `a^n ≤ 1 + a^{2n}`. -/
private theorem Theorem26Flow.im_pow_le {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (E : ℝ) {η₁ η₂ : ℝ} (h1 : 0 < η₁)
    (h12 : η₁ ≤ η₂) (n : ℕ) :
    (RBM.stieltjes H ((E : ℂ) + (η₁ : ℂ) * Complex.I)).im ^ n ≤
      (η₂ / η₁) ^ n * ((Fintype.card ι : ℝ)⁻¹ *
        ∑ x, (1 + ‖green H ((E : ℂ) + (η₂ : ℂ) * Complex.I) x x‖ ^ (2 * n))) := by
  set c : ℝ := (Fintype.card ι : ℝ) with hcdef
  have hc : 0 < c := by rw [hcdef]; exact_mod_cast Fintype.card_pos
  set a := (RBM.stieltjes H ((E : ℂ) + (η₁ : ℂ) * Complex.I)).im with hadef
  set b := (RBM.stieltjes H ((E : ℂ) + (η₂ : ℂ) * Complex.I)).im with hbdef
  set g : ι → ℝ := fun x => ‖green H ((E : ℂ) + (η₂ : ℂ) * Complex.I) x x‖ with hgdef
  have ha0 : 0 ≤ a := by
    rw [hadef, stieltjes_im_eq_normalized_specWeight H hH E η₁ h1]
    refine mul_nonneg (by positivity) (Finset.sum_nonneg fun l _ => ?_)
    positivity
  have hab : a ≤ η₂ / η₁ * b := by
    have := stieltjes_eta_mul_im_mono H hH E η₁ η₂ h1 h12
    rw [div_mul_eq_mul_div, le_div_iff₀ h1]
    linarith
  have hbg : b ≤ c⁻¹ * ∑ x, g x := by
    refine (Complex.im_le_norm _).trans ?_
    unfold RBM.stieltjes
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    unfold Matrix.trace Matrix.diag
    exact norm_sum_le _ _
  have hg0 : ∀ x, 0 ≤ g x := fun x => norm_nonneg _
  have hmean0 : 0 ≤ c⁻¹ * ∑ x, g x :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun x _ => hg0 x)
  have hjensen : (c⁻¹ * ∑ x, g x) ^ n ≤ c⁻¹ * ∑ x, g x ^ n := by
    have hw : ∑ _x : ι, c⁻¹ = 1 := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hcdef, mul_inv_cancel₀ hc.ne']
    have := Real.pow_arith_mean_le_arith_mean_pow Finset.univ (fun _ => c⁻¹) g
      (fun _ _ => by positivity) hw (fun x _ => hg0 x) n
    rw [Finset.mul_sum, Finset.mul_sum]
    exact this
  have hpow : ∀ x, g x ^ n ≤ 1 + g x ^ (2 * n) := by
    intro x
    rw [pow_mul', sq]
    nlinarith [sq_nonneg (g x ^ n - 1)]
  have hq0 : 0 ≤ η₂ / η₁ := div_nonneg (h1.le.trans h12) h1.le
  calc a ^ n ≤ (η₂ / η₁ * (c⁻¹ * ∑ x, g x)) ^ n := by
        refine pow_le_pow_left₀ ha0 (hab.trans ?_) n
        exact mul_le_mul_of_nonneg_left hbg hq0
    _ = (η₂ / η₁) ^ n * (c⁻¹ * ∑ x, g x) ^ n := mul_pow _ _ _
    _ ≤ (η₂ / η₁) ^ n * (c⁻¹ * ∑ x, g x ^ n) :=
        mul_le_mul_of_nonneg_left hjensen (pow_nonneg hq0 _)
    _ ≤ (η₂ / η₁) ^ n * (c⁻¹ * ∑ x, (1 + g x ^ (2 * n))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun x _ => hpow x) (by positivity)) (pow_nonneg hq0 _)

/-- **The a priori bound `AprioriImM` on the common OU carrier**, from the single-scale local law
`FlowLocalLaw` at `t = 0`: `Im m(E+i/N) ≤ N^{2τ} Im m(E+iN^{-1+2τ}) ≤ N^{2τ} N^{-1} ∑_x |G_xx|`. -/
theorem aprioriImM_of_flowLocalLaw (d : Dims) {κ : ℝ} (hκ : 0 < κ) {τ0 : ℝ} (hτ0 : 0 < τ0)
    (hLL : ∀ τU, 0 < τU → τU ≤ τ0 → FlowLocalLaw d κ τU) :
    AprioriImM (ouCommonFlow d) κ := by
  intro E hE n ε hε
  -- parameters fixed before `N`
  set τ : ℝ := min τ0 (ε / (4 * ((n : ℝ) + 1))) with hτdef
  have hτ : 0 < τ := lt_min hτ0 (by positivity)
  have hττ0 : τ ≤ τ0 := min_le_left _ _
  have hτn : 2 * (n : ℝ) * τ ≤ ε / 2 := by
    have h1 : τ ≤ ε / (4 * ((n : ℝ) + 1)) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at h1
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  have hsize : Tendsto (fun N => ((ouCommonBand d).size N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (ouCommonBand d).tendsto_size
  have ev2 : ∀ᶠ N : ℕ in atTop, (2 : ℝ) ≤ ((ouCommonBand d).size N : ℝ) ^ (ε / 4) :=
    ((tendsto_rpow_atTop (by positivity)).comp hsize).eventually_ge_atTop _
  have hE' : |E| ≤ 2 - κ / 2 := by linarith
  filter_upwards [hLL τ hτ hττ0 (ε / 4) (by positivity) n, ev2] with N hLLN h2
  set X : ℝ := ((ouCommonBand d).size N : ℝ) with hXdef
  have hX1 : 1 ≤ X := Theorem26Flow.one_le_size d N
  have hX0 : 0 < X := by linarith
  set η₁ : ℝ := X⁻¹ with hη₁def
  set η₂ : ℝ := X ^ (-1 + 2 * τ) with hη₂def
  have hη₁ : 0 < η₁ := inv_pos.2 hX0
  have hη₂ : 0 < η₂ := Real.rpow_pos_of_pos hX0 _
  have h12 : η₁ ≤ η₂ := by
    rw [hη₁def, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
  have hq : η₂ / η₁ = X ^ (2 * τ) := by
    rw [hη₁def, hη₂def, div_inv_eq_mul, ← Real.rpow_add_one hX0.ne']
    ring_nf
  have hcard := Theorem26Flow.card_idx d N
  have : Nonempty (d.Idx N) := ⟨(0, ⟨0, d.W_pos N⟩)⟩
  set z₂ : ℂ := (E : ℂ) + (η₂ : ℂ) * Complex.I with hz₂def
  have hz₂ : 0 < z₂.im := by simp [hz₂def, hη₂]
  -- integrability of the local-law integrand
  have hIG : ∀ x : d.Idx N, Integrable (fun ω =>
      ‖green ((ouCommonFlow d).Ht N 0 ω) z₂ x x‖ ^ (2 * n)) (ouCommonMeasure d) := by
    intro x
    refine Integrable.of_bound
      ((Theorem26Flow.measurable_green d N 0 z₂ x x).norm.pow_const _).aestronglyMeasurable
      (z₂.im⁻¹ ^ (2 * n)) (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) ((RBM.norm_apply_le_l2_opNorm _ x x).trans
      (norm_green_le ((ouCommonFlow d).hermitian N 0 ω) hz₂ (le_abs_self _))) _
  have hIG1 : ∀ x : d.Idx N, Integrable (fun ω =>
      1 + ‖green ((ouCommonFlow d).Ht N 0 ω) z₂ x x‖ ^ (2 * n)) (ouCommonMeasure d) :=
    fun x => (integrable_const (1 : ℝ)).add (hIG x)
  have hIg : Integrable (fun ω => (η₂ / η₁) ^ n * ((Fintype.card (d.Idx N) : ℝ)⁻¹ *
      ∑ x : d.Idx N, (1 + ‖green ((ouCommonFlow d).Ht N 0 ω) z₂ x x‖ ^ (2 * n))))
      (ouCommonMeasure d) :=
    ((integrable_finsetSum _ fun x _ => hIG1 x).const_mul _).const_mul _
  have hzη₁ : ((E : ℂ) + ((((ouCommonBand d).size N : ℝ))⁻¹ : ℂ) * Complex.I) =
      (E : ℂ) + (η₁ : ℂ) * Complex.I := by
    rw [hη₁def, hXdef, Complex.ofReal_inv]
  change ∫ ω, (RBM.stieltjes ((ouCommonFlow d).Ht N 0 ω)
      ((E : ℂ) + ((((ouCommonBand d).size N : ℝ))⁻¹ : ℂ) * Complex.I)).im ^ n
      ∂(ouCommonMeasure d) ≤ X ^ ε
  simp_rw [hzη₁]
  refine (integral_mono_of_nonneg (Eventually.of_forall fun ω => ?_) hIg
    (Eventually.of_forall fun ω => ?_)).trans ?_
  · refine pow_nonneg ?_ n
    rw [stieltjes_im_eq_normalized_specWeight _ ((ouCommonFlow d).hermitian N 0 ω) E η₁ hη₁]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun l _ => by positivity)
  · exact Theorem26Flow.im_pow_le ((ouCommonFlow d).hermitian N 0 ω) E hη₁ h12 n
  · rw [integral_const_mul, integral_const_mul,
      integral_finsetSum _ fun x _ => hIG1 x]
    have hsum : ∑ x : d.Idx N, ∫ ω, (1 + ‖green ((ouCommonFlow d).Ht N 0 ω) z₂ x x‖ ^ (2 * n))
        ∂(ouCommonMeasure d) ≤ ∑ _x : d.Idx N, (1 + X ^ (ε / 4)) := by
      refine Finset.sum_le_sum fun x _ => ?_
      rw [integral_add (integrable_const 1) (hIG x), integral_const, probReal_univ,
        smul_eq_mul, mul_one]
      have := hLLN 0 ⟨le_rfl, (Real.rpow_pos_of_pos hX0 _).le⟩ E hE' x
      linarith
    have hmean : (Fintype.card (d.Idx N) : ℝ)⁻¹ * ∑ x : d.Idx N,
        ∫ ω, (1 + ‖green ((ouCommonFlow d).Ht N 0 ω) z₂ x x‖ ^ (2 * n)) ∂(ouCommonMeasure d) ≤
        1 + X ^ (ε / 4) := by
      refine (mul_le_mul_of_nonneg_left hsum (by positivity)).trans (le_of_eq ?_)
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀
        (by rw [hcard]; exact hX0.ne'), one_mul]
    have hX4 : 1 ≤ X ^ (ε / 4) := Real.one_le_rpow hX1 (by positivity)
    have h1X : 1 + X ^ (ε / 4) ≤ X ^ (ε / 2) := by
      have : X ^ (ε / 2) = X ^ (ε / 4) * X ^ (ε / 4) := by
        rw [← Real.rpow_add hX0]; ring_nf
      rw [this]; nlinarith
    have hqn : (η₂ / η₁) ^ n ≤ X ^ (ε / 2) := by
      rw [hq, ← Real.rpow_natCast, ← Real.rpow_mul hX0.le]
      exact Real.rpow_le_rpow_of_exponent_le hX1 (by nlinarith)
    have hq0 : 0 ≤ (η₂ / η₁) ^ n := pow_nonneg (div_nonneg hη₂.le hη₁.le) _
    calc (η₂ / η₁) ^ n * ((Fintype.card (d.Idx N) : ℝ)⁻¹ * ∑ x : d.Idx N,
          ∫ ω, (1 + ‖green ((ouCommonFlow d).Ht N 0 ω) z₂ x x‖ ^ (2 * n)) ∂(ouCommonMeasure d))
        ≤ X ^ (ε / 2) * X ^ (ε / 2) :=
          mul_le_mul hqn (hmean.trans h1X) (by
            refine mul_nonneg (by positivity) (Finset.sum_nonneg fun x _ => ?_)
            exact integral_nonneg fun ω => by positivity) (Real.rpow_pos_of_pos hX0 _).le
      _ = X ^ ε := by rw [← Real.rpow_add hX0]; ring_nf

/-! ### Step 2 output, `Step2Output d κ` -/

private theorem Theorem26Flow.ouMatrix_measurable (d : Dims) (N : ℕ) (t : ℝ) :
    Measurable (ouMatrix d N t) := by
  rw [show ouMatrix d N t = ouInterpolatedMatrix d N t from
    funext (ouMatrix_eq_interpolatedMatrix d N t)]
  apply measurable_pi_iff.mpr; intro i
  apply measurable_pi_iff.mpr; intro j
  have hs : Measurable (ouInterpolatedSample d N t) := by
    apply measurable_pi_iff.mpr; intro c
    simp only [ouInterpolatedSample]; fun_prop
  exact (measurable_Xentry d N i j).comp hs

/-- Law transfer at `t = 0`: the band pairing is the carrier pairing of `H_0`. -/
private theorem Theorem26Flow.bandPairing_eq (d : Dims) (N k : ℕ) {O : (Fin k → ℝ) → ℝ}
    (hO : Continuous O) (E : ℝ) :
    bandPairing d N k O E =
      RBM.corrPairing (ouCommonBand d).P ((ouCommonFlow d).Ht N 0)
        ((ouCommonFlow d).hermitian N 0) k O E := by
  have hstart : ouMatrix d N 0 = (fun ω : Ω d × Ω d => Xmat d N ω.1) :=
    funext fun ω => ouMatrix_start d N ω
  have hlaw : (P d).map (Xmat d N) = (ouCommonMeasure d).map ((ouCommonFlow d).Ht N 0) := by
    have h := (ouCommonFlowLaw d).law N 0 le_rfl
    change (ouCommonMeasure d).map ((ouCommonFlow d).Ht N 0) = _ at h
    rw [h, hstart]
    have hfst : (fun ω : Ω d × Ω d => Xmat d N ω.1) = Xmat d N ∘ Prod.fst := rfl
    rw [hfst, ← Measure.map_map (measurable_Xmat d N) measurable_fst, ouProductMeasure,
      Measure.map_fst_prod, measure_univ, one_smul]
  exact corrPairing_congr_law (P d) (ouCommonMeasure d) (measurable_Xmat d N)
    (ouCommonFlow_measurable d N 0) (Xmat_isHermitian d N) ((ouCommonFlow d).hermitian N 0)
    hlaw k hO E

/-- Law transfer at `t ≥ 0`: the OU-marginal pairing is the carrier pairing of `H_t`. -/
private theorem Theorem26Flow.ouPairing_eq (d : Dims) (N : ℕ) {t : ℝ} (ht : 0 ≤ t) (k : ℕ)
    {O : (Fin k → ℝ) → ℝ} (hO : Continuous O) (E : ℝ) :
    ouPairing d N t k O E =
      RBM.corrPairing (ouCommonBand d).P ((ouCommonFlow d).Ht N t)
        ((ouCommonFlow d).hermitian N t) k O E :=
  corrPairing_congr_law (ouProductMeasure d N) (ouCommonMeasure d)
    (Theorem26Flow.ouMatrix_measurable d N t) (ouCommonFlow_measurable d N t)
    (ouMatrix_isHermitian d N t) ((ouCommonFlow d).hermitian N t)
    ((ouCommonFlowLaw d).law N t ht).symm k hO E

/-- **G5 terminal: Step 2 output in the interface** (`Step2Output d κ`, `τU ∈ (0,1)`),
consumed by `theorem2_6_mat_of_steps`. -/
theorem step2Output_of_flow (d : Dims) {κ : ℝ} (hκ : 0 < κ) {τ0 : ℝ} (hτ0 : 0 < τ0)
    (hLL : ∀ τU, 0 < τU → τU ≤ τ0 → FlowLocalLaw d κ τU)
    (hQUE : ∀ τU, 0 < τU → τU ≤ τ0 → FlowEq747 d κ τU) :
    Step2Output d κ := by
  intro E hE k
  have hc := d.c_pos
  have hden : (0 : ℝ) < 48 * k + 2 := by positivity
  set τ : ℝ := min (min τ0 (d.c / 6)) (min (d.c / 36 / (48 * k + 2)) (1 / 2)) with hτdef
  have hτ : 0 < τ := lt_min (lt_min hτ0 (by positivity)) (lt_min (by positivity) (by norm_num))
  have hτ1 : τ < 1 := lt_of_le_of_lt ((min_le_right _ _).trans (min_le_right _ _)) (by norm_num)
  have hττ0 : τ ≤ τ0 := (min_le_left _ _).trans (min_le_left _ _)
  have hτc : τ < d.c / 3 :=
    lt_of_le_of_lt ((min_le_left _ _).trans (min_le_right _ _)) (by linarith)
  have hτk : τ * (48 * k + 2) ≤ d.c / 36 :=
    (le_div_iff₀ hden).1 ((min_le_right _ _).trans (min_le_left _ _))
  refine ⟨τ, hτ, hτ1, fun O hO => ?_⟩
  obtain ⟨K, hK⟩ := corrPairing_sub_le_of_claim223 (ouCommonFlow d) (ouCommonFlow_measurable d)
    hO hτ (by norm_num : (0 : ℝ) ≤ 24)
    (fun n _ => claim223_of_flow d hκ hτ hτc (hLL τ hτ hττ0) (hQUE τ hτ hττ0) E hE n)
    (fun n _ => aprioriImM_of_flowLocalLaw d hκ hτ0 hLL E hE n)
  have hexp : -(d.c / 36) + 24 * (k : ℝ) * τ < 0 := by
    have hk0 : (0 : ℝ) ≤ k * τ := mul_nonneg (Nat.cast_nonneg k) hτ.le
    nlinarith
  have hlim := (((Theorem26Flow.tendsto_rpow d hexp).add
    (Theorem26Flow.tendsto_rpow d (by linarith : -(τ / 2) < 0))).add
    (Theorem26Flow.tendsto_rpow d (by norm_num : -(1 / 2 : ℝ) < 0))).const_mul K
  simp only [add_zero, mul_zero] at hlim
  have htU : ∀ N, 0 ≤ (ouCommonBand d).tPow τ N := fun N =>
    (Real.rpow_pos_of_pos (by linarith [Theorem26Flow.one_le_size d N]) _).le
  refine squeeze_zero_norm' (hK.mono fun N hN => ?_) hlim
  rw [Real.norm_eq_abs, Theorem26Flow.bandPairing_eq d N k hO.1.continuous E,
    show (Gauss.band d).tPow τ N = (ouCommonBand d).tPow τ N from rfl,
    Theorem26Flow.ouPairing_eq d N (htU N) k hO.1.continuous E]
  exact hN

/-! ### Checks -/

end RBM.Gauss
