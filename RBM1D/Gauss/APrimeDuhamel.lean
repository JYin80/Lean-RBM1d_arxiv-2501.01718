/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.SampleFlowBridge

/-!
# The `∇χ` term and the same-time quadratic-variation rates (T260)

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.2–§5.3: **steps 5 and 6** of route (A′).  Steps 1–4 are
`RBM1D/Gauss/APrimeTestFun.lean` (T250), `RBM1D/Gauss/APrimeRatioBdd.lean` (T255) and
`RBM1D/Gauss/SampleFlowBridge.lean` (T259); the estimate of (5.39)–(5.47) — step 7 — is not
touched here.

## Step 5: the `∇χ` term inside the `u`-Duhamel

The generator identity `RBM.Gauss.hasDerivAt_integral_Phi` differentiates `u ↦ E[Φ(H_u)]`
pointwise in `u`; what the moment field needs is the **increment** over a window.  The two
pieces are

* `RBM.Gauss.coordD2_mul` — the Leibniz expansion `∂²_α(W·Ψ) = (∂²_α W)Ψ + 2(∂_αW)(∂_αΨ) +
  W(∂²_αΨ)`, which is what makes the `∇χ` term nameable at all;
* `RBM.Gauss.norm_integral_sub_le_of_genTerm_le` — the closure: a bound on the generator term
  over `[a,b]` bounds the increment by `C·(b−a)`.  **No constant-coefficient Grönwall**: the
  bound on the generator term is not assumed proportional to the quantity estimated.

The `∇χ` term is bounded with **no cardinality loss**:

* `RBM.Gauss.norm_fderiv_softMax_ratio_le` — `‖∇ J̃‖ ≤ card^{1/(2r)}·(b₁/T₀)`, i.e.
  `RBM.Step2Bootstrap.abs_deriv_softMax_le_affine` at `Λ = 0`, `K = b₁/T₀`, read off the
  Fréchet derivative.  The factor `2r` of `RBM.Gauss.norm_fderiv_sum_ratio_pow_le` is exactly
  cancelled by the outer exponent `1/(2r)`, and `Y^{1/(2r)−1}·Y^{1−1/(2r)} = 1`.
* `RBM.Gauss.norm_fderiv_softW_ratio_le` — the same for the weight, with `|χ'| ≤ 15/8`
  (`RBM.Cutoff.abs_cutChiD_le`); where `Y = 0` the weight is locally constant `1`, which is the
  neighbourhood form of `RBM.Step2Bootstrap.cutChiD_softW_eq_zero`.
* `RBM.Gauss.norm_fderiv_softW_ratio_le_exp`, `RBM.Gauss.sum_gvar_gradChi_le_exp` — calibrated
  by `RBM.Step2Bootstrap.rpow_card_le_exp_one`: `card^{1/(2r)}` becomes `e`.
* `RBM.Gauss.norm_lk_le_of_softW_ne_zero` — the a priori bound on the transition band,
  `RBM.Step2Bootstrap.abs_le_two_mul_of_softW_ne_zero` on the model's own (5.29) family:
  where the weight is non-zero, *every* loop obeys `‖L−K‖ ≤ 2Θ·Θ_N·T_{u,D}`, again with no
  cardinality factor.

## Step 6: the two same-time quadratic-variation rates

`RBM.Step2Bootstrap.sum_gvar_mul_le_sqrt_quadVar` splits the mixed covariation into
`√(quadVar F)·√(quadVar G)`; what was missing were the rates themselves on the model.

* `RBM.Gauss.coordWeight` — `∑_α S_α‖B_α‖²`, the model's own coordinate weight;
* `RBM.Gauss.quadVar_le_of_bddC2C` — `quadVar F ≤ b₁²·coordWeight`;
* `RBM.Gauss.quadVar_loopObs_sub_le` — the `(+,−)` loop of (5.29), i.e. the numerator `L − K`,
  with the constant of `RBM.Gauss.bddC2C_loopObs_sub`;
* `RBM.Gauss.quadVar_psi_le`, `RBM.Gauss.sum_gvar_cross_le` — the moment factor's rate and the
  closed cross term.

## What is **not** here

* Step 7, the estimate of (5.39)–(5.47) (near field `≲ R^{7/2}/R^8`, far field
  `≲ R·A^{−1/3}R^4`).  Three tickets have declined to reconstruct those two exponents from
  §5.3; nothing here endorses them.
* A **cardinality-free second-derivative** bound on `Y = ∑_i ρ_i^{2r}`.  The `∇²χ` term of
  `RBM.Gauss.coordD2_mul` is the one place where the only available constant is the uniform
  one of `RBM.Gauss.bddC2C_sum_of_uniform`, which carries a full factor `card S`.  The
  Duhamel closure here therefore uses `RBM.Gauss.TestFun.bdd₂` for that term
  (`RBM.Gauss.norm_genTerm_le`), which is correct but not sharp.  See the report.
-/

namespace RBM

namespace Gauss

open scoped Matrix.Norms.L2Operator

open MeasureTheory Step2Bootstrap Cutoff

/-! ### 1. Leibniz for the coordinate derivatives -/

section Leibniz

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {A B : E → ℂ}

/-- The product rule for a directional derivative. -/
theorem fderiv_mul_apply (hA : ContDiff ℝ 1 A) (hB : ContDiff ℝ 1 B) (M V : E) :
    fderiv ℝ (fun M => A M * B M) M V = fderiv ℝ A M V * B M + A M * fderiv ℝ B M V := by
  have hd := ((hA.differentiable one_ne_zero M).hasFDerivAt).mul
    ((hB.differentiable one_ne_zero M).hasFDerivAt)
  have h : fderiv ℝ (fun M => A M * B M) M = A M • fderiv ℝ B M + B M • fderiv ℝ A M := by
    simpa [Pi.mul_def] using hd.fderiv
  rw [h]
  simp [smul_eq_mul]
  ring

/-- **The second-order Leibniz rule along one coordinate direction.** -/
theorem fderiv2_mul_apply (hA : ContDiff ℝ 2 A) (hB : ContDiff ℝ 2 B) (M V : E) :
    fderiv ℝ (fderiv ℝ (fun M => A M * B M)) M V V
      = fderiv ℝ (fderiv ℝ A) M V V * B M
        + 2 * (fderiv ℝ A M V * fderiv ℝ B M V)
        + A M * fderiv ℝ (fderiv ℝ B) M V V := by
  have hA1 : ContDiff ℝ 1 A := hA.of_le (by norm_num)
  have hB1 : ContDiff ℝ 1 B := hB.of_le (by norm_num)
  have hAB : ContDiff ℝ 2 (fun M => A M * B M) := hA.mul hB
  have key := hasDerivAt_dir2 hAB M V
  have hfun : (fun t : ℝ => fderiv ℝ (fun M => A M * B M) (M + t • V) V)
      = fun t : ℝ => fderiv ℝ A (M + t • V) V * B (M + t • V)
          + A (M + t • V) * fderiv ℝ B (M + t • V) V :=
    funext fun t => fderiv_mul_apply hA1 hB1 (M + t • V) V
  rw [hfun] at key
  have h1 : HasDerivAt (fun t : ℝ => fderiv ℝ A (M + t • V) V)
      (fderiv ℝ (fderiv ℝ A) M V V) 0 := hasDerivAt_dir2 hA M V
  have h2 : HasDerivAt (fun t : ℝ => B (M + t • V)) (fderiv ℝ B M V) 0 := by
    simpa using hasDerivAt_dir hB1 M V 0
  have h3 : HasDerivAt (fun t : ℝ => A (M + t • V)) (fderiv ℝ A M V) 0 := by
    simpa using hasDerivAt_dir hA1 M V 0
  have h4 : HasDerivAt (fun t : ℝ => fderiv ℝ B (M + t • V) V)
      (fderiv ℝ (fderiv ℝ B) M V V) 0 := hasDerivAt_dir2 hB M V
  have hprod := (h1.mul h2).add (h3.mul h4)
  simp only [zero_smul, add_zero] at hprod
  have := key.unique hprod
  rw [this]
  ring

variable {d : Dims} {N : ℕ}

/-- `RBM.Gauss.fderiv_mul_apply` in the coordinate vocabulary. -/
theorem coordD1_mul {A B : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}
    (hA : ContDiff ℝ 1 A) (hB : ContDiff ℝ 1 B)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) (q : d.Idx N × d.Idx N × Bool) :
    coordD1 d N (fun M => A M * B M) M q
      = coordD1 d N A M q * B M + A M * coordD1 d N B M q :=
  fderiv_mul_apply hA hB M _

/-- **⭐ The Leibniz expansion of the generator's second-order coefficient.**  The three
terms are, in order, the `∇²χ` term, the cross term of step 6, and the main term. -/
theorem coordD2_mul {A B : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}
    (hA : ContDiff ℝ 2 A) (hB : ContDiff ℝ 2 B)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) (q : d.Idx N × d.Idx N × Bool) :
    coordD2 d N (fun M => A M * B M) M q
      = coordD2 d N A M q * B M + 2 * (coordD1 d N A M q * coordD1 d N B M q)
        + A M * coordD2 d N B M q :=
  fderiv2_mul_apply hA hB M _

/-- The triangle inequality applied to `RBM.Gauss.coordD2_mul`. -/
theorem norm_coordD2_mul_le {A B : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}
    (hA : ContDiff ℝ 2 A) (hB : ContDiff ℝ 2 B)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) (q : d.Idx N × d.Idx N × Bool) :
    ‖coordD2 d N (fun M => A M * B M) M q‖
      ≤ ‖coordD2 d N A M q‖ * ‖B M‖ + 2 * (‖coordD1 d N A M q‖ * ‖coordD1 d N B M q‖)
        + ‖A M‖ * ‖coordD2 d N B M q‖ := by
  rw [coordD2_mul hA hB M q]
  refine (norm_add_le _ _).trans ?_
  refine add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_
  · exact le_of_eq (norm_mul _ _)
  · rw [norm_mul, norm_mul]
    simp
  · exact le_of_eq (norm_mul _ _)

end Leibniz

/-! ### 2. The gradient of the soft-max weight, free of `card` -/

section WeightGrad

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} {S : Finset ι} {F : ι → E → ℂ} {T : ι → ℝ} {b₀ b₁ b₂ T₀ Θ : ℝ} {r : ℕ}

/-- `Y = ∑_i ρ_i^{2r}` is `C²` whenever each numerator is and the denominators have a floor. -/
theorem contDiff_sum_ratio_pow (hT₀ : 0 < T₀) (hT : ∀ i ∈ S, T₀ ≤ T i)
    (hF : ∀ i ∈ S, BddC2C (F i) b₀ b₁ b₂) (r : ℕ) :
    ContDiff ℝ 2 (fun M : E => ∑ i ∈ S, (‖F i M‖ / T i) ^ (2 * r)) :=
  (bddC2C_sum_of_uniform S
    (fun i hi => bddC2C_ratio_pow_of_le hT₀ (hT i hi) (hF i hi) r)).contDiff

/-- **⭐ The gradient of the soft maximum of the model's ratios carries only `card^{1/(2r)}`.**

This is `RBM.Step2Bootstrap.abs_deriv_softMax_le_affine` at `Λ = 0` and `K = b₁/T₀`, read
directly off the Fréchet derivative: the factor `2r` of
`RBM.Gauss.norm_fderiv_sum_ratio_pow_le` is exactly cancelled by the exponent `1/(2r)` of the
outer root, and `Y^{1/(2r)-1} · Y^{1-1/(2r)} = 1`.  `RBM.Step2Bootstrap.rpow_card_le_exp_one`
turns the remaining `card^{1/(2r)}` into `e`. -/
theorem norm_fderiv_softMax_ratio_le (hT₀ : 0 < T₀) (hb₁ : 0 ≤ b₁) (hT : ∀ i ∈ S, T₀ ≤ T i)
    (hF : ∀ i ∈ S, BddC2C (F i) b₀ b₁ b₂) (hr : 1 ≤ r) (M : E)
    (hY : 0 < ∑ i ∈ S, (‖F i M‖ / T i) ^ (2 * r)) :
    ‖fderiv ℝ (fun M => softMax r S (fun i => ‖F i M‖ / T i)) M‖
      ≤ (S.card : ℝ) ^ ((1 : ℝ) / (2 * (r : ℝ))) * (b₁ / T₀) := by
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hn0 : (0 : ℝ) < 2 * (r : ℝ) := by linarith
  set a : ℝ := (1 : ℝ) / (2 * (r : ℝ)) with ha
  have ha0 : 0 < a := by rw [ha]; positivity
  set Y : E → ℝ := fun M => ∑ i ∈ S, (‖F i M‖ / T i) ^ (2 * r) with hYdef
  have hYc : ContDiff ℝ 2 Y := contDiff_sum_ratio_pow hT₀ hT hF r
  have hd : HasFDerivAt Y (fderiv ℝ Y M) M := (hYc.differentiable (by norm_num) M).hasFDerivAt
  have hrp : HasFDerivAt (fun M => Y M ^ a) ((a * Y M ^ (a - 1)) • fderiv ℝ Y M) M :=
    hd.rpow_const (Or.inl hY.ne')
  have hfun : (fun M : E => softMax r S (fun i => ‖F i M‖ / T i)) = fun M => Y M ^ a := rfl
  rw [hfun, hrp.fderiv, norm_smul, Real.norm_eq_abs]
  have hYa : (0 : ℝ) < Y M ^ (a - 1) := Real.rpow_pos_of_pos hY _
  have habs : |a * Y M ^ (a - 1)| = a * Y M ^ (a - 1) := abs_of_pos (by positivity)
  rw [habs]
  have hgrad := norm_fderiv_sum_ratio_pow_le S hT₀ hb₁ hT hF hr M
  have hcast : ((2 * r : ℕ) : ℝ) = 2 * (r : ℝ) := by push_cast; ring
  rw [hcast] at hgrad
  have hb : (0 : ℝ) ≤ b₁ / T₀ := div_nonneg hb₁ hT₀.le
  have hcard : (0 : ℝ) ≤ (S.card : ℝ) ^ a := Real.rpow_nonneg (Nat.cast_nonneg _) _
  calc a * Y M ^ (a - 1) * ‖fderiv ℝ Y M‖
      ≤ a * Y M ^ (a - 1) *
          ((2 * (r : ℝ)) * ((S.card : ℝ) ^ a * Y M ^ (1 - a)) * (b₁ / T₀)) := by
        exact mul_le_mul_of_nonneg_left hgrad (by positivity)
    _ = ((2 * (r : ℝ)) * a) * (Y M ^ (a - 1) * Y M ^ (1 - a)) * ((S.card : ℝ) ^ a * (b₁ / T₀)) := by
        ring
    _ = (S.card : ℝ) ^ a * (b₁ / T₀) := by
        have h1 : Y M ^ (a - 1) * Y M ^ (1 - a) = 1 := by
          rw [← Real.rpow_add hY]
          norm_num
        have h2 : (2 * (r : ℝ)) * a = 1 := by
          rw [ha]; field_simp
        rw [h1, h2]; ring

/-- **⭐ The gradient of the weight itself.**  `χ' ≤ 15/8` (`RBM.Cutoff.abs_cutChiD_le`) and
the chain rule; where `Y = 0` the weight is locally constant `1`
(`RBM.Step2Bootstrap.cutChiD_softW_eq_zero` is the pointwise form of the same fact), so the
bound holds on all of `E`. -/
theorem norm_fderiv_softW_ratio_le (hΘ : 0 < Θ) (hT₀ : 0 < T₀) (hb₁ : 0 ≤ b₁)
    (hT : ∀ i ∈ S, T₀ ≤ T i) (hF : ∀ i ∈ S, BddC2C (F i) b₀ b₁ b₂) (hr : 1 ≤ r) (M : E) :
    ‖fderiv ℝ (fun M => softW r S (fun i => ‖F i M‖ / T i) Θ) M‖
      ≤ (15 / 8) / Θ * ((S.card : ℝ) ^ ((1 : ℝ) / (2 * (r : ℝ))) * (b₁ / T₀)) := by
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hn0 : (0 : ℝ) < 2 * (r : ℝ) := by linarith
  set a : ℝ := (1 : ℝ) / (2 * (r : ℝ)) with ha
  have ha0 : (0 : ℝ) ≤ a := by rw [ha]; positivity
  set Y : E → ℝ := fun M => ∑ i ∈ S, (‖F i M‖ / T i) ^ (2 * r) with hYdef
  set σ : E → ℝ := fun M => softMax r S (fun i => ‖F i M‖ / T i) with hσdef
  have hYc : ContDiff ℝ 2 Y := contDiff_sum_ratio_pow hT₀ hT hF r
  have hb : (0 : ℝ) ≤ b₁ / T₀ := div_nonneg hb₁ hT₀.le
  have hcard : (0 : ℝ) ≤ (S.card : ℝ) ^ a := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hrhs : (0 : ℝ) ≤ (15 / 8) / Θ * ((S.card : ℝ) ^ a * (b₁ / T₀)) := by positivity
  rcases eq_or_lt_of_le (sum_even_pow_nonneg S (fun i => ‖F i M‖ / T i) r) with hY0 | hY
  · -- `Y M = 0`: the weight is constant `1` near `M`.
    have hσeq : σ M = Y M ^ a := rfl
    have hσ0 : σ M = 0 := by
      have hYM0 : Y M = 0 := hY0.symm
      rw [hσeq, hYM0, Real.zero_rpow]
      rw [ha]; positivity
    have hcont : ContinuousAt σ M := by
      have h1 : ContinuousAt Y M := (hYc.continuous).continuousAt
      have h2 : ContinuousAt (fun y : ℝ => y ^ a) (Y M) :=
        Real.continuousAt_rpow_const _ _ (Or.inr ha0)
      exact h2.comp h1
    have hnb : ∀ᶠ M' in nhds M, σ M' < Θ := by
      have := hcont (Iio_mem_nhds (by rw [hσ0]; exact hΘ))
      exact this
    have heq : (fun M' : E => softW r S (fun i => ‖F i M'‖ / T i) Θ)
        =ᶠ[nhds M] fun _ : E => (1 : ℝ) := by
      filter_upwards [hnb] with M' hM'
      exact cutChi_eq_one ((div_le_one hΘ).2 hM'.le)
    rw [heq.fderiv_eq]
    simpa using hrhs
  · -- `Y M > 0`: the chain rule.
    have hd : HasFDerivAt Y (fderiv ℝ Y M) M := (hYc.differentiable (by norm_num) M).hasFDerivAt
    have hσd : HasFDerivAt σ ((a * Y M ^ (a - 1)) • fderiv ℝ Y M) M :=
      hd.rpow_const (Or.inl hY.ne')
    have hdiv : HasFDerivAt (fun M' => σ M' / Θ)
        (Θ⁻¹ • ((a * Y M ^ (a - 1)) • fderiv ℝ Y M)) M := by
      have := hσd.const_mul (Θ⁻¹ : ℝ)
      simpa [div_eq_inv_mul] using this
    have hchain := (hasDerivAt_cutChi (σ M / Θ)).comp_hasFDerivAt M hdiv
    have hfun : (fun M' : E => softW r S (fun i => ‖F i M'‖ / T i) Θ)
        = cutChi ∘ fun M' => σ M' / Θ := rfl
    rw [hfun, hchain.fderiv, norm_smul, Real.norm_eq_abs]
    have hgrad : ‖Θ⁻¹ • ((a * Y M ^ (a - 1)) • fderiv ℝ Y M)‖
        ≤ Θ⁻¹ * ((S.card : ℝ) ^ a * (b₁ / T₀)) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hΘ)]
      refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hΘ.le)
      have := norm_fderiv_softMax_ratio_le hT₀ hb₁ hT hF hr M hY
      rw [hσd.fderiv] at this
      exact this
    calc |cutChiD (σ M / Θ)| * ‖Θ⁻¹ • ((a * Y M ^ (a - 1)) • fderiv ℝ Y M)‖
        ≤ (15 / 8) * (Θ⁻¹ * ((S.card : ℝ) ^ a * (b₁ / T₀))) :=
          mul_le_mul (abs_cutChiD_le _) hgrad (norm_nonneg _) (by norm_num)
      _ = (15 / 8) / Θ * ((S.card : ℝ) ^ a * (b₁ / T₀)) := by
          rw [div_eq_mul_inv]; ring

/-- **The calibrated form**: at `2r ≥ A log n` with `card S ≤ n^A`, the `card^{1/(2r)}` of
`RBM.Gauss.norm_fderiv_softW_ratio_le` is the constant `e`
(`RBM.Step2Bootstrap.rpow_card_le_exp_one`). -/
theorem norm_fderiv_softW_ratio_le_exp {A : ℝ} {n : ℕ} (hΘ : 0 < Θ) (hT₀ : 0 < T₀)
    (hb₁ : 0 ≤ b₁) (hT : ∀ i ∈ S, T₀ ≤ T i) (hF : ∀ i ∈ S, BddC2C (F i) b₀ b₁ b₂)
    (hr : 1 ≤ r) (hS : S.Nonempty) (hn : 2 ≤ n) (hA : 0 < A)
    (hcard : ((S.card : ℝ)) ≤ (n : ℝ) ^ A) (hq : A * Real.log n ≤ 2 * (r : ℝ)) (M : E) :
    ‖fderiv ℝ (fun M => softW r S (fun i => ‖F i M‖ / T i) Θ) M‖
      ≤ (15 / 8) / Θ * (Real.exp 1 * (b₁ / T₀)) := by
  have hc0 : (0 : ℝ) < (S.card : ℝ) := by
    exact_mod_cast Finset.card_pos.2 hS
  have hkey := rpow_card_le_exp_one (c := (S.card : ℝ)) (q := 2 * (r : ℝ)) hc0 hn hcard hA hq
  refine (norm_fderiv_softW_ratio_le hΘ hT₀ hb₁ hT hF hr M).trans ?_
  have hb : (0 : ℝ) ≤ b₁ / T₀ := div_nonneg hb₁ hT₀.le
  have hΘ' : (0 : ℝ) ≤ (15 / 8) / Θ := by positivity
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hkey hb) hΘ'

end WeightGrad

/-! ### 3. The transition band: the a priori bound with no cardinality loss -/

section Band

variable {d : Dims} {N : ℕ} {E D u ΘN Θ : ℝ} {r : ℕ}

open Step2

/-- **⭐ The a priori bound the `∇χ` term consumes, on the model's own (5.29) family.**
Where the weight of route (A′) does not vanish, *every* loop of the family satisfies
`‖(L−K)_{u,(+,−),a}‖ ≤ 2Θ · Θ_N · T_{u,D}(a)` — with no cardinality factor, because
`RBM.Step2Bootstrap.le_softMax` dominates the maximum by the soft maximum pointwise. -/
theorem norm_lk_le_of_softW_ne_zero (hr : 1 ≤ r) (hΘ : 0 < Θ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ)
    (hne : softW r (Finset.univ : Finset (LoopArg (d.L N) 2))
        (fun a => ‖loopObs d N (zt E u)
              (LoopData.idx ((Step2.sigPM, a) : LoopData (d.L N) 2)) M
            - (band d).Kval E N u (LoopData.idx ((Step2.sigPM, a) : LoopData (d.L N) 2))‖
          / (ΘN * tailT ((d.W N : ℝ)) ((band d).ell N u) (etaT E u) D
              ((zdist (d.L N) (a 0 - a 1) : ℝ)))) Θ ≠ 0)
    (a : LoopArg (d.L N) 2) (hpos : 0 < ΘN * tailT ((d.W N : ℝ)) ((band d).ell N u)
        (etaT E u) D ((zdist (d.L N) (a 0 - a 1) : ℝ))) :
    ‖loopObs d N (zt E u) (LoopData.idx ((Step2.sigPM, a) : LoopData (d.L N) 2)) M
        - (band d).Kval E N u (LoopData.idx ((Step2.sigPM, a) : LoopData (d.L N) 2))‖
      ≤ 2 * Θ * (ΘN * tailT ((d.W N : ℝ)) ((band d).ell N u) (etaT E u) D
          ((zdist (d.L N) (a 0 - a 1) : ℝ))) := by
  have h := abs_le_two_mul_of_softW_ne_zero hr hΘ hne (Finset.mem_univ a)
  rw [abs_of_nonneg (div_nonneg (norm_nonneg _) hpos.le)] at h
  rw [← div_le_iff₀ hpos] at *
  exact h

end Band

/-! ### 4. Step 6 — the two same-time quadratic-variation rates -/

section QuadVar

variable {d : Dims} {N : ℕ}

/-- The model's coordinate weight `∑_α S_α ‖B_α‖²`: a deterministic constant of the band
model, carrying no dependence on the observable. -/
noncomputable def coordWeight (d : Dims) (N : ℕ) : ℝ :=
  ∑ q ∈ usedCoord d N, (gvar d (crd d N q) : ℝ) * ‖Bmat d N q.1 q.2.1 q.2.2‖ ^ 2

theorem coordWeight_nonneg (d : Dims) (N : ℕ) : 0 ≤ coordWeight d N :=
  Finset.sum_nonneg fun q _ => mul_nonneg (gvar d (crd d N q)).2 (by positivity)

/-- **⭐ The same-time quadratic-variation rate of a quantitative `C²` observable.**
`quadVar = ∑_α S_α ‖∂_α F‖²` and `‖∂_α F‖ ≤ b₁‖B_α‖`, so the rate is `b₁²` times the model
constant.  This is the form `RBM.Step2Bootstrap.sum_gvar_mul_le_sqrt_quadVar` consumes. -/
theorem quadVar_le_of_bddC2C {F : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} {b₀ b₁ b₂ : ℝ}
    (hF : BddC2C F b₀ b₁ b₂) (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    quadVar d N F M ≤ b₁ ^ 2 * coordWeight d N := by
  rw [quadVar, coordWeight, Finset.mul_sum]
  refine Finset.sum_le_sum fun q _ => ?_
  have hb : ‖coordD1 d N F M q‖ ≤ b₁ * ‖Bmat d N q.1 q.2.1 q.2.2‖ := by
    rw [coordD1]
    exact ((fderiv ℝ F M).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hF.bdd₁ M) (norm_nonneg _))
  have hsq : ‖coordD1 d N F M q‖ ^ 2 ≤ (b₁ * ‖Bmat d N q.1 q.2.1 q.2.2‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hb 2
  calc (gvar d (crd d N q) : ℝ) * ‖coordD1 d N F M q‖ ^ 2
      ≤ (gvar d (crd d N q) : ℝ) * (b₁ * ‖Bmat d N q.1 q.2.1 q.2.2‖) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (gvar d (crd d N q)).2
    _ = b₁ ^ 2 * ((gvar d (crd d N q) : ℝ) * ‖Bmat d N q.1 q.2.1 q.2.2‖ ^ 2) := by ring

/-- **⭐⭐ The first of the two model-side rates**: the `(+,−)` loop of (5.29), i.e. the
numerator `L − K` of route (A′)'s ratio family.  The constant is the one
`RBM.Gauss.bddC2C_loopObs_sub` supplies, `b₁ = card(Idx N)·n·B^n` with `n = 2`. -/
theorem quadVar_loopObs_sub_le {z : ℂ} {η B : ℝ} (hz : z.im ≠ 0) (hη : 0 < η)
    (hzη : η ≤ |z.im|) (hBa : η⁻¹ ≤ B) (hBb : η⁻¹ * η⁻¹ ≤ B)
    (hBc : 2 * (η⁻¹ * η⁻¹ * η⁻¹) ≤ B) {I : LoopIdx (ZMod (d.L N))} (hwf : I.WF) (K : ℂ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    quadVar d N (fun M => loopObs d N z I M - K) M
      ≤ ((Fintype.card (d.Idx N) : ℝ) * ((I.a.length : ℝ) * B ^ I.a.length) + 0) ^ 2
        * coordWeight d N :=
  quadVar_le_of_bddC2C (bddC2C_loopObs_sub hz hη hzη hBa hBb hBc hwf K) M

/-- **⭐⭐ The second rate**: the moment factor `Ψ`.  Any `RBM.Gauss.BddC2C` observable has
the same shape of rate, so the two sides of `sum_gvar_mul_le_sqrt_quadVar` are symmetric. -/
theorem quadVar_psi_le {Ψ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} {c₀ c₁ c₂ : ℝ}
    (hΨ : BddC2C Ψ c₀ c₁ c₂) (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    quadVar d N Ψ M ≤ c₁ ^ 2 * coordWeight d N :=
  quadVar_le_of_bddC2C hΨ M

/-- **⭐ The cross term of the Leibniz expansion, bounded by the two same-time rates.**
`RBM.Step2Bootstrap.sum_gvar_mul_le_sqrt_quadVar` splits the mixed covariation into
`√(quadVar F)·√(quadVar G)`, and the two rates above close it. -/
theorem sum_gvar_cross_le {F G : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} {b₀ b₁ b₂ c₀ c₁ c₂ : ℝ}
    (hF : BddC2C F b₀ b₁ b₂) (hG : BddC2C G c₀ c₁ c₂)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    ∑ q ∈ usedCoord d N, (gvar d (crd d N q) : ℝ) *
        (‖coordD1 d N F M q‖ * ‖coordD1 d N G M q‖)
      ≤ b₁ * c₁ * coordWeight d N := by
  refine (sum_gvar_mul_le_sqrt_quadVar d N F G M).trans ?_
  have hw : 0 ≤ coordWeight d N := coordWeight_nonneg d N
  have h1 : √(quadVar d N F M) ≤ b₁ * √(coordWeight d N) := by
    have := Real.sqrt_le_sqrt (quadVar_le_of_bddC2C hF M)
    rwa [Real.sqrt_mul (by positivity), Real.sqrt_sq hF.nonneg₁] at this
  have h2 : √(quadVar d N G M) ≤ c₁ * √(coordWeight d N) := by
    have := Real.sqrt_le_sqrt (quadVar_le_of_bddC2C hG M)
    rwa [Real.sqrt_mul (by positivity), Real.sqrt_sq hG.nonneg₁] at this
  calc √(quadVar d N F M) * √(quadVar d N G M)
      ≤ (b₁ * √(coordWeight d N)) * (c₁ * √(coordWeight d N)) :=
        mul_le_mul h1 h2 (Real.sqrt_nonneg _)
          (mul_nonneg hF.nonneg₁ (Real.sqrt_nonneg _))
    _ = b₁ * c₁ * (√(coordWeight d N) * √(coordWeight d N)) := by ring
    _ = b₁ * c₁ * coordWeight d N := by rw [Real.mul_self_sqrt hw]

end QuadVar

/-! ### 5. Step 5 — the generator identity integrated in `u` -/

section Duhamel

variable {d : Dims} {N : ℕ} {Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}

/-- The generator term of `RBM.Gauss.hasDerivAt_integral_Phi`, as a function of the time.
This is the `u`-integrand of the Duhamel. -/
noncomputable def genTerm (d : Dims) (N : ℕ) (Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ)
    (v : ℝ) : ℂ :=
  (1 / 2 : ℝ) • ∑ q ∈ usedCoord d N, (gvar d (crd d N q) : ℝ) •
    ∫ ω, coordD2 d N Φ (Hflow d N v ω) q ∂(P d)

/-- **⭐⭐ The Duhamel closure of route (A′), step 5.**

`RBM.Gauss.hasDerivAt_integral_Phi` gives the derivative of `u ↦ E[Φ(H_u)]` at every positive
time; integrating it along the window with the mean value inequality turns a bound on the
generator term into a bound on the *increment* of the moment — which is the shape
`RBM.Step2Bootstrap.weightedMoment_of_stepBound` consumes at each net point.

**No constant-coefficient Grönwall is used**: the bound on the generator term is not assumed
proportional to the quantity being estimated. -/
theorem norm_integral_sub_le_of_genTerm_le (hst : MatrixStein d) (h : TestFun d N Φ)
    {a b C : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hC : ∀ v ∈ Set.Icc a b, ‖genTerm d N Φ v‖ ≤ C) :
    ‖(∫ ω, Φ (Hflow d N b ω) ∂(P d)) - (∫ ω, Φ (Hflow d N a ω) ∂(P d))‖ ≤ C * (b - a) := by
  have hderiv : ∀ v ∈ Set.Icc a b,
      HasDerivWithinAt (fun s : ℝ => ∫ ω, Φ (Hflow d N s ω) ∂(P d))
        (genTerm d N Φ v) (Set.Icc a b) v := fun v hv =>
    (hasDerivAt_integral_Phi hst h (lt_of_lt_of_le ha hv.1)).hasDerivWithinAt
  have hmvt := (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hC
    (Set.left_mem_Icc.2 hab) (Set.right_mem_Icc.2 hab)
  calc ‖(∫ ω, Φ (Hflow d N b ω) ∂(P d)) - (∫ ω, Φ (Hflow d N a ω) ∂(P d))‖
      ≤ C * ‖b - a‖ := hmvt
    _ = C * (b - a) := by rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]

/-- **The generator term of a `RBM.Gauss.TestFun` is bounded by `½ C₂ · ∑_α S_α‖B_α‖²`.**
The constant is the one `RBM.Gauss.TestFun.bdd₂` supplies, and `RBM.Gauss.coordWeight` is the
model's own coordinate weight — the same constant the two `quadVar` rates of §4 carry. -/
theorem norm_genTerm_le {C₂ : ℝ}
    (hC₂ : ∀ M, ‖fderiv ℝ (fderiv ℝ Φ) M‖ ≤ C₂) (v : ℝ) :
    ‖genTerm d N Φ v‖ ≤ (1 / 2 : ℝ) * (C₂ * coordWeight d N) := by
  have := isProbabilityMeasure_P d
  have hterm : ∀ q ∈ usedCoord d N,
      ‖(gvar d (crd d N q) : ℝ) • ∫ ω, coordD2 d N Φ (Hflow d N v ω) q ∂(P d)‖
        ≤ (gvar d (crd d N q) : ℝ) * (C₂ * ‖Bmat d N q.1 q.2.1 q.2.2‖ ^ 2) := by
    intro q _
    have hgv : |((gvar d (crd d N q) : ℝ))| = ((gvar d (crd d N q) : ℝ)) :=
      abs_of_nonneg (gvar d (crd d N q)).2
    have hb : ∀ ω : Ω d, ‖coordD2 d N Φ (Hflow d N v ω) q‖
        ≤ C₂ * ‖Bmat d N q.1 q.2.1 q.2.2‖ ^ 2 := by
      intro ω
      have hx := norm_coordD2_le hC₂ (Hflow d N v ω) q
      calc ‖coordD2 d N Φ (Hflow d N v ω) q‖
          ≤ C₂ * ‖Bmat d N q.1 q.2.1 q.2.2‖ * ‖Bmat d N q.1 q.2.1 q.2.2‖ := hx
        _ = C₂ * ‖Bmat d N q.1 q.2.1 q.2.2‖ ^ 2 := by ring
    have hint : ‖∫ ω, coordD2 d N Φ (Hflow d N v ω) q ∂(P d)‖
        ≤ C₂ * ‖Bmat d N q.1 q.2.1 q.2.2‖ ^ 2 := by
      have := norm_integral_le_of_norm_le_const (μ := P d)
        (f := fun ω => coordD2 d N Φ (Hflow d N v ω) q)
        (C := C₂ * ‖Bmat d N q.1 q.2.1 q.2.2‖ ^ 2) (Filter.Eventually.of_forall hb)
      simpa using this
    rw [norm_smul, Real.norm_eq_abs, hgv]
    exact mul_le_mul_of_nonneg_left hint (gvar d (crd d N q)).2
  rw [genTerm, norm_smul, Real.norm_eq_abs, show |(1 / 2 : ℝ)| = 1 / 2 by norm_num]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  rw [coordWeight, Finset.mul_sum]
  exact Finset.sum_congr rfl fun q _ => by ring

/-- **⭐ Step 5, assembled**: for a `RBM.Gauss.TestFun` the increment of the moment over a
window is at most `½ C₂ · coordWeight · (b − a)`.  With `RBM.Gauss.testFun_softW_jS` as `Φ`
this is route (A′)'s one-step Duhamel. -/
theorem norm_integral_sub_le_testFun (hst : MatrixStein d) (h : TestFun d N Φ) {C₂ : ℝ}
    (hC₂ : ∀ M, ‖fderiv ℝ (fderiv ℝ Φ) M‖ ≤ C₂) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ‖(∫ ω, Φ (Hflow d N b ω) ∂(P d)) - (∫ ω, Φ (Hflow d N a ω) ∂(P d))‖
      ≤ (1 / 2 : ℝ) * (C₂ * coordWeight d N) * (b - a) :=
  norm_integral_sub_le_of_genTerm_le hst h ha hab (fun v _ => norm_genTerm_le hC₂ v)

/-- The same statement in `RBM.Sample` vocabulary, which is what
`RBM.Step2Bootstrap.WeightedMoment` is quantified over.  The bridge is definitional
(`RBM.Gauss.integral_sample_H_eq`). -/
theorem norm_integral_sample_sub_le_testFun (hst : MatrixStein d) (h : TestFun d N Φ)
    {C₂ : ℝ} (hC₂ : ∀ M, ‖fderiv ℝ (fderiv ℝ Φ) M‖ ≤ C₂) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) :
    ‖(∫ ω, Φ ((sample d).H N b ω) ∂(band d).P)
        - (∫ ω, Φ ((sample d).H N a ω) ∂(band d).P)‖
      ≤ (1 / 2 : ℝ) * (C₂ * coordWeight d N) * (b - a) :=
  norm_integral_sub_le_testFun hst h hC₂ ha hab

end Duhamel

/-! ### 6. The `∇χ` term of the Leibniz expansion, with no cardinality loss -/

section GradChi

variable {d : Dims} {N : ℕ} {ι : Type*} {S : Finset ι}
variable {F : ι → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} {T : ι → ℝ}
variable {Ψ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}
variable {b₀ b₁ b₂ c₀ c₁ c₂ T₀ Θ : ℝ} {r : ℕ}

/-- **⭐⭐ The `∇χ` term of the generator, bounded with no cardinality loss.**

This is the middle term of `RBM.Gauss.coordD2_mul` — the one in which the derivative hits the
cutoff — weighted by the Gaussian variances exactly as `RBM.Gauss.genTerm` weights it.  The
weight's gradient is `RBM.Gauss.norm_fderiv_softW_ratio_le` (card-free up to
`card^{1/(2r)}`), the moment factor's is `RBM.Gauss.BddC2C.bdd₁`, and the coordinate sum is
the model constant `RBM.Gauss.coordWeight` — the same one that carries the two `quadVar`
rates of §4, so `RBM.Step2Bootstrap.sum_gvar_mul_le_sqrt_quadVar` gives the identical answer
through the Cauchy–Schwarz route. -/
theorem sum_gvar_gradChi_le (hΘ : 0 < Θ) (hT₀ : 0 < T₀) (hb₁ : 0 ≤ b₁)
    (hT : ∀ i ∈ S, T₀ ≤ T i) (hF : ∀ i ∈ S, BddC2C (F i) b₀ b₁ b₂) (hr : 1 ≤ r)
    (hΨ : BddC2C Ψ c₀ c₁ c₂) (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    ∑ q ∈ usedCoord d N, (gvar d (crd d N q) : ℝ) *
        (‖fderiv ℝ (fun M => softW r S (fun i => ‖F i M‖ / T i) Θ) M
              (Bmat d N q.1 q.2.1 q.2.2)‖ * ‖coordD1 d N Ψ M q‖)
      ≤ ((15 / 8) / Θ * ((S.card : ℝ) ^ ((1 : ℝ) / (2 * (r : ℝ))) * (b₁ / T₀))) * c₁
        * coordWeight d N := by
  set Kw : ℝ := (15 / 8) / Θ * ((S.card : ℝ) ^ ((1 : ℝ) / (2 * (r : ℝ))) * (b₁ / T₀)) with hKw
  have hKw0 : 0 ≤ Kw := by
    rw [hKw]
    have : (0 : ℝ) ≤ b₁ / T₀ := div_nonneg hb₁ hT₀.le
    have hc : (0 : ℝ) ≤ (S.card : ℝ) ^ ((1 : ℝ) / (2 * (r : ℝ))) :=
      Real.rpow_nonneg (Nat.cast_nonneg _) _
    positivity
  have hgrad := norm_fderiv_softW_ratio_le hΘ hT₀ hb₁ hT hF hr
  rw [coordWeight, Finset.mul_sum]
  refine Finset.sum_le_sum fun q _ => ?_
  have h1 : ‖fderiv ℝ (fun M => softW r S (fun i => ‖F i M‖ / T i) Θ) M
      (Bmat d N q.1 q.2.1 q.2.2)‖ ≤ Kw * ‖Bmat d N q.1 q.2.1 q.2.2‖ := by
    refine ((fderiv ℝ (fun M => softW r S (fun i => ‖F i M‖ / T i) Θ) M).le_opNorm _).trans ?_
    exact mul_le_mul_of_nonneg_right (hgrad M) (norm_nonneg _)
  have h2 : ‖coordD1 d N Ψ M q‖ ≤ c₁ * ‖Bmat d N q.1 q.2.1 q.2.2‖ :=
    norm_coordD1_le hΨ.bdd₁ M q
  have hprod : ‖fderiv ℝ (fun M => softW r S (fun i => ‖F i M‖ / T i) Θ) M
        (Bmat d N q.1 q.2.1 q.2.2)‖ * ‖coordD1 d N Ψ M q‖
      ≤ (Kw * ‖Bmat d N q.1 q.2.1 q.2.2‖) * (c₁ * ‖Bmat d N q.1 q.2.1 q.2.2‖) :=
    mul_le_mul h1 h2 (norm_nonneg _) (mul_nonneg hKw0 (norm_nonneg _))
  calc (gvar d (crd d N q) : ℝ) *
        (‖fderiv ℝ (fun M => softW r S (fun i => ‖F i M‖ / T i) Θ) M
          (Bmat d N q.1 q.2.1 q.2.2)‖ * ‖coordD1 d N Ψ M q‖)
      ≤ (gvar d (crd d N q) : ℝ) *
          ((Kw * ‖Bmat d N q.1 q.2.1 q.2.2‖) * (c₁ * ‖Bmat d N q.1 q.2.1 q.2.2‖)) :=
        mul_le_mul_of_nonneg_left hprod (gvar d (crd d N q)).2
    _ = Kw * c₁ * ((gvar d (crd d N q) : ℝ) * ‖Bmat d N q.1 q.2.1 q.2.2‖ ^ 2) := by ring

/-- **The calibrated `∇χ` bound**: `card^{1/(2r)}` replaced by `e`. -/
theorem sum_gvar_gradChi_le_exp {A : ℝ} {n : ℕ} (hΘ : 0 < Θ) (hT₀ : 0 < T₀) (hb₁ : 0 ≤ b₁)
    (hc₁ : 0 ≤ c₁) (hT : ∀ i ∈ S, T₀ ≤ T i) (hF : ∀ i ∈ S, BddC2C (F i) b₀ b₁ b₂)
    (hr : 1 ≤ r) (hΨ : BddC2C Ψ c₀ c₁ c₂) (hS : S.Nonempty) (hn : 2 ≤ n) (hA : 0 < A)
    (hcard : ((S.card : ℝ)) ≤ (n : ℝ) ^ A) (hq : A * Real.log n ≤ 2 * (r : ℝ))
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    ∑ q ∈ usedCoord d N, (gvar d (crd d N q) : ℝ) *
        (‖fderiv ℝ (fun M => softW r S (fun i => ‖F i M‖ / T i) Θ) M
              (Bmat d N q.1 q.2.1 q.2.2)‖ * ‖coordD1 d N Ψ M q‖)
      ≤ ((15 / 8) / Θ * (Real.exp 1 * (b₁ / T₀))) * c₁ * coordWeight d N := by
  have hc0 : (0 : ℝ) < (S.card : ℝ) := by exact_mod_cast Finset.card_pos.2 hS
  have hkey := rpow_card_le_exp_one (c := (S.card : ℝ)) (q := 2 * (r : ℝ)) hc0 hn hcard hA hq
  refine (sum_gvar_gradChi_le hΘ hT₀ hb₁ hT hF hr hΨ M).trans ?_
  have hb : (0 : ℝ) ≤ b₁ / T₀ := div_nonneg hb₁ hT₀.le
  have hΘ' : (0 : ℝ) ≤ (15 / 8) / Θ := by positivity
  have hstep : (15 / 8) / Θ * ((S.card : ℝ) ^ ((1 : ℝ) / (2 * (r : ℝ))) * (b₁ / T₀))
      ≤ (15 / 8) / Θ * (Real.exp 1 * (b₁ / T₀)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hkey hb) hΘ'
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hstep hc₁) (coordWeight_nonneg d N)

end GradChi

/-! ### 7. The degenerate exponent `p = 0` -/

section PZero

open MeasureTheory MomentDuhamelCut

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The `p = 0` branch of `RBM.Step2Bootstrap.WeightedMoment` is trivial, and has to be
taken separately.**  At `p = 0` the integrand degenerates to the weight itself: the pointwise
domination by the soft-max object (`RBM.Gauss.abs_cutTrunc_jS_pow_le`) becomes `1 ≤ 1` and
carries no information, so the Duhamel is never invoked.  The bound is instead the a priori
`0 ≤ W ≤ 1` on a probability space. -/
theorem integral_weight_pow_zero_le {P : Measure Ω} [IsProbabilityMeasure P] {W : Ω → ℝ}
    {J : Ω → ℝ} {θ : ℝ} (hW0 : ∀ ω, 0 ≤ W ω) (hW1 : ∀ ω, W ω ≤ 1)
    (hWm : AEStronglyMeasurable W P) :
    ∫ ω, W ω * |cutTrunc θ (J ω)| ^ (2 * 0) ∂P ≤ 1 := by
  have hfun : (fun ω => W ω * |cutTrunc θ (J ω)| ^ (2 * 0)) = fun ω => W ω := by
    funext ω; simp
  rw [hfun]
  have hint : Integrable W P :=
    ⟨hWm, by
      refine (hasFiniteIntegral_const (1 : ℝ)).mono ?_
      filter_upwards with ω
      rw [Real.norm_eq_abs, abs_of_nonneg (hW0 ω), Real.norm_eq_abs, abs_one]
      exact hW1 ω⟩
  calc ∫ ω, W ω ∂P ≤ ∫ _ω, (1 : ℝ) ∂P :=
        integral_mono hint (integrable_const 1) hW1
    _ = 1 := by simp

end PZero

/-! ### 8. Compiled satisfiability witnesses -/

section Sat

open Step2 MeasureTheory

/-- The test function of `RBM.Gauss.sat_testFun_softW_jS`, named so that the Duhamel closure
can be stated on it. -/
noncomputable def satPhi (N : ℕ) :
    Matrix (Dims.exampleGrow.Idx N) (Dims.exampleGrow.Idx N) ℂ → ℂ :=
  fun M => ((softW 1 (Finset.univ : Finset (LoopArg (Dims.exampleGrow.L N) 2))
      (fun a => ‖loopObs Dims.exampleGrow N (zt 0 (1 / 2))
            (LoopData.idx ((Step2.sigPM, a) : LoopData (Dims.exampleGrow.L N) 2)) M
          - (band Dims.exampleGrow).Kval 0 N (1 / 2)
              (LoopData.idx ((Step2.sigPM, a) : LoopData (Dims.exampleGrow.L N) 2))‖
        / (1 * tailT ((Dims.exampleGrow.W N : ℝ)) ((band Dims.exampleGrow).ell N (1 / 2))
            (etaT 0 (1 / 2)) 1 ((zdist (Dims.exampleGrow.L N) (a 0 - a 1) : ℝ)))) 1 : ℝ) : ℂ)
    * (1 : ℂ)

theorem sat_testFun_satPhi (N : ℕ) : TestFun Dims.exampleGrow N (satPhi N) :=
  sat_testFun_softW_jS N

/-- **⭐ A compiled witness for step 5.**  Every hypothesis of
`RBM.Gauss.norm_integral_sub_le_testFun` holds simultaneously on the concrete model
`RBM.Gauss.Dims.exampleGrow`, at the genuine `(+,−)` soft-max weight of (5.29) — `MatrixStein`
is `RBM.Gauss.matrixStein`, the `RBM.Gauss.TestFun` is `RBM.Gauss.sat_testFun_softW_jS`, and
the second-derivative constant comes from its own `bdd₂`.  Nothing here is discharged by a
constant `Φ`: `RBM.Gauss.softRootProfile_ne_const` shows the cutoff really cuts. -/
theorem sat_norm_integral_sub_le (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a b : ℝ, 0 < a → a ≤ b →
      ‖(∫ ω, satPhi N (Hflow Dims.exampleGrow N b ω) ∂(P Dims.exampleGrow))
          - (∫ ω, satPhi N (Hflow Dims.exampleGrow N a ω) ∂(P Dims.exampleGrow))‖
        ≤ C * (b - a) := by
  obtain ⟨C₂, hC₂⟩ := (sat_testFun_satPhi N).bdd₂
  have hC₂0 : (0 : ℝ) ≤ C₂ :=
    le_trans (norm_nonneg (fderiv ℝ (fderiv ℝ (satPhi N)) 0)) (hC₂ 0)
  refine ⟨(1 / 2 : ℝ) * (C₂ * coordWeight Dims.exampleGrow N),
    mul_nonneg (by norm_num) (mul_nonneg hC₂0 (coordWeight_nonneg _ _)), fun a b ha hab => ?_⟩
  exact norm_integral_sub_le_testFun (matrixStein _) (sat_testFun_satPhi N) hC₂ ha hab

/-- **⭐ A compiled witness for step 6**: the same-time quadratic-variation rate of the genuine
`(+,−)` loop of (5.29) on `RBM.Gauss.Dims.exampleGrow`, with the constant of
`RBM.Gauss.bddC2C_loopObs_sub` and the model's own coordinate weight.  The loop is the real
two-edge one, not a constant. -/
theorem sat_quadVar_loopObs_sub (N : ℕ) (a : LoopArg (Dims.exampleGrow.L N) 2)
    (M : Matrix (Dims.exampleGrow.Idx N) (Dims.exampleGrow.Idx N) ℂ) :
    ∃ b₁ : ℝ, 0 ≤ b₁ ∧
      quadVar Dims.exampleGrow N (fun M => loopObs Dims.exampleGrow N (zt 0 (1 / 2))
          (LoopData.idx ((Step2.sigPM, a) : LoopData (Dims.exampleGrow.L N) 2)) M
        - (band Dims.exampleGrow).Kval 0 N (1 / 2)
            (LoopData.idx ((Step2.sigPM, a) : LoopData (Dims.exampleGrow.L N) 2))) M
        ≤ b₁ ^ 2 * coordWeight Dims.exampleGrow N := by
  have hE : |(0 : ℝ)| < 2 := by norm_num
  have hη : (0 : ℝ) < etaT 0 (1 / 2) := etaT_pos' hE (by norm_num)
  have hz : (zt 0 (1 / 2 : ℝ)).im ≠ 0 := by rw [← etaT_eq_zt_im]; exact hη.ne'
  have hzη : etaT 0 (1 / 2) ≤ |(zt 0 (1 / 2 : ℝ)).im| := by
    rw [← etaT_eq_zt_im, abs_of_pos hη]
  have hx0 : (0 : ℝ) < (etaT 0 (1 / 2))⁻¹ := by positivity
  have key : ∀ x : ℝ, 0 < x →
      x ≤ 2 * (1 + x) ^ 3 ∧ x * x ≤ 2 * (1 + x) ^ 3 ∧ 2 * (x * x * x) ≤ 2 * (1 + x) ^ 3 := by
    intro x hx
    refine ⟨by nlinarith [sq_nonneg x, hx.le], by nlinarith [sq_nonneg x, hx.le],
      by nlinarith [sq_nonneg x, hx.le]⟩
  obtain ⟨hBa, hBb, hBc⟩ := key _ hx0
  have hbdd := bddC2C_loopObs_sub (d := Dims.exampleGrow) (N := N) hz hη hzη hBa hBb hBc
    (LoopData.idx_wf ((Step2.sigPM, a) : LoopData (Dims.exampleGrow.L N) 2))
    ((band Dims.exampleGrow).Kval 0 N (1 / 2)
      (LoopData.idx ((Step2.sigPM, a) : LoopData (Dims.exampleGrow.L N) 2)))
  exact ⟨_, hbdd.nonneg₁, quadVar_le_of_bddC2C hbdd M⟩

end Sat

end Gauss

end RBM

/-!
## Deviations from the paper

**T260a** (§5.2, the generator/Stein computation; §5.3, (5.39)–(5.47)).

1. *The Duhamel is closed by the mean value inequality, not by the fundamental theorem of
   calculus.*  The paper integrates the generator identity in `u` along the window.  In Lean
   `intervalIntegral.integral_eq_sub_of_hasDerivAt` needs the derivative to be interval
   integrable, which would require continuity of `u ↦ E[∂²Φ(H_u)]` — a fact nobody in this
   repository has proved.  `RBM.Gauss.norm_integral_sub_le_of_genTerm_le` therefore uses
   `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le` and a uniform bound on the generator
   term over the window, giving `C·(b−a)` in place of `∫_a^b G(u) du`.  This is weaker only
   in that it cannot exploit a `u`-dependent rate; on a window `[s_N, t_N]` with monotone
   constants it is the same bound.  No change to the paper is proposed.  Affects the display
   after (5.29) where the integration in `u` is performed.  ~40 lines.  No renumbering.
2. *The `∇²χ` term is bounded by the uniform second-derivative constant of
   `RBM.Gauss.TestFun`, not by a cardinality-free one.*  The paper's accounting treats all
   derivative hits on the cutoff on the same footing.  Here the first-order hit is
   cardinality-free (`RBM.Gauss.sum_gvar_gradChi_le_exp`: constant `e`) while the second-order
   hit is not, because the repository has no sharp bound on `‖D²(∑_i ρ_i^{2r})‖` — only
   `RBM.Gauss.bddC2C_sum_of_uniform`, whose constant carries a factor `card S`.  The bound
   stated is therefore correct but loses `card` in that one term.  Closing this needs one new
   lemma (the second-derivative analogue of `RBM.Gauss.norm_fderiv_sum_ratio_pow_le`), not a
   change to the paper.  Affects nothing in the text.  ~0 lines of paper change.  No
   renumbering.
-/
