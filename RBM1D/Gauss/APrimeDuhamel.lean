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

/-! ### 8. The vector bound (S2) and the cross term (S5) of the Stein route

⚠ **These replace the `∇²χ` accounting of §5–§6 above, not the `∇χ` one.**  The referee's
ruling (V548, §6) is that the global `C²` mean-value closure cannot produce a one-step moment
bound: the main estimate goes through the Stein identity (★), where `∇²` only ever hits the
resolvent factor `F_u` and `∇²χ` never appears.  What the cross term needs instead is a bound
on the **quadratic-variation rate** of the soft maximum in which the constant is the *random*
rate of the numerators, not a deterministic derivative bound.

`RBM.Step2Bootstrap.abs_deriv_softMax_le_affine` is a **scalar** statement: for one fixed
coordinate `α` it turns `|∂_α ρ_i| ≤ Λ|ρ_i| + K` into `|∂_α J̃| ≤ Λ J̃ + card^{1/q} K`.  Summing
that over `α` is not enough, because `∑_α σ_α · max_i |∂_α ρ_i|²` and
`max_i ∑_α σ_α |∂_α ρ_i|²` differ by as much as `card S` (V548, appendix B); and taking for
`K` the deterministic first-derivative constant `b₁` of `RBM.Gauss.BddC2C` gives a bound that
is true but useless.  `RBM.Gauss.sqrt_quadVar_softMax_le` below is the **vector** form: it
performs Minkowski in `ℓ²(usedCoord, gvar)` *before* Hölder in `i`, so the constant that comes
out is `max_i √(quadVar f_i)/c_i` — a random, same-time quadratic-variation rate, which
`RBM.EarlyQVRate.quadVar_lkFun_le_ee_sym` supplies on the model.

Main results:

* `RBM.Gauss.sqrt_wsum_add_le`, `RBM.Gauss.sqrt_wsum_sum_le` — Minkowski for a finite sum in
  a weighted `ℓ²` over a `Finset`, the one step the scalar brick was missing.
* `RBM.Gauss.abs_fderiv_ratio_pow_apply_le` — the **directional** derivative of one ratio
  power, `|∂_B ρ_i^{2r}| ≤ 2r ρ_i^{2r-1}‖∂_B f_i‖/c_i`: the numerator's own derivative in the
  same direction, never a uniform constant.
* `RBM.Gauss.abs_fderiv_softMax_apply_le` — the same for `J̃ = Y^{1/(2r)}`.
* `RBM.Gauss.sqrt_quadVar_softMax_le` — **(S2)**:
  `√(quadVar J̃) ≤ card^{1/(2r)} · max_i √(quadVar f_i)/c_i`.
* `RBM.Gauss.sqrt_quadVar_softW_pow_le` — the same for the weight `W = χ(J̃/Θ)^{2p}`, with
  `|χ'| ≤ 15/8` (`RBM.Cutoff.abs_cutChiD_le`); at `Y = 0` the weight is locally constant `1`
  and both sides vanish, so no hypothesis excludes the configuration `L = K`.
* `RBM.Gauss.sqrt_quadVar_norm_pow_le` — the moment factor's own rate,
  `√(quadVar |Ψ|^{2p}) ≤ 2p‖Ψ‖^{2p-1}√(quadVar Ψ)`.
* `RBM.Gauss.quadVar_softW_pow_eq_zero_of_outside_band` — the `1_{S′}` of (S5): off the
  transition band `Θ ≤ J̃ ≤ 2Θ` the weight's rate is exactly `0`, because the chain rule's
  factor is `χ'(J̃/Θ)`.
* `RBM.Gauss.sum_gvar_crossTerm_le` — **(S5)**, the cross term's pointwise bound.
* `RBM.Gauss.satLk`, `RBM.Gauss.exists_bddC2C_satLk`,
  `RBM.Gauss.sat_sum_gvar_crossTerm_le` — a compiled satisfiability witness: every hypothesis
  of (S5) holds simultaneously on `RBM.Gauss.Dims.exampleGrow` at the genuine two-edge `(+,−)`
  loop family, for **every** `r, p ≥ 1`, every `Θ > 0` and every `M` — including `L = K`.

**Both gradients are taken in the same matrix variable `M`.**  Every statement below is a
pointwise inequality at one `M : Matrix (d.Idx N) (d.Idx N) ℂ`, and `coordD1 d N · M q` is
used for the weight and for the moment factor alike.  The rescaling `M ↦ lk_{u_j,b}(√(u_j/u)M)`
that this forces on the earlier-time loops, and the factor `√(u_j/u)` its `coordD1` picks up,
belong to the caller: `√u_j ≤ 1` is absorbed into `κ̂_j` and `u^{-1/2}` into the time integral
(S6).  Nothing here silently mixes two variables.
-/

section VectorQV

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {κ ι : Type*}

/-! #### 8.1 Minkowski in a weighted `ℓ²` over a `Finset` -/

/-- Two-term Minkowski for a weighted `ℓ²` sum over a `Finset`. -/
theorem sqrt_wsum_add_le (T : Finset κ) (σ : κ → ℝ) (hσ : ∀ q ∈ T, 0 ≤ σ q) (x y : κ → ℝ) :
    √(∑ q ∈ T, σ q * (x q + y q) ^ 2)
      ≤ √(∑ q ∈ T, σ q * x q ^ 2) + √(∑ q ∈ T, σ q * y q ^ 2) := by
  set A : ℝ := ∑ q ∈ T, σ q * x q ^ 2 with hA
  set Bq : ℝ := ∑ q ∈ T, σ q * y q ^ 2 with hB
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun q hq => mul_nonneg (hσ q hq) (sq_nonneg _)
  have hB0 : 0 ≤ Bq := Finset.sum_nonneg fun q hq => mul_nonneg (hσ q hq) (sq_nonneg _)
  set a : κ → ℝ := fun q => √(σ q) * x q with ha
  set b : κ → ℝ := fun q => √(σ q) * y q with hb
  have hsq : ∀ q ∈ T, √(σ q) ^ 2 = σ q := fun q hq => Real.sq_sqrt (hσ q hq)
  have hA' : ∑ q ∈ T, a q ^ 2 = A := by
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [ha, mul_pow, hsq q hq]
  have hB' : ∑ q ∈ T, b q ^ 2 = Bq := by
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [hb, mul_pow, hsq q hq]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq T a b
  rw [hA', hB'] at hcs
  have hcross : ∑ q ∈ T, σ q * (x q * y q) ≤ √A * √Bq := by
    have h1 : ∑ q ∈ T, a q * b q = ∑ q ∈ T, σ q * (x q * y q) := by
      refine Finset.sum_congr rfl fun q hq => ?_
      have hmm : √(σ q) * √(σ q) = σ q := Real.mul_self_sqrt (hσ q hq)
      simp only [ha, hb]
      calc (√(σ q) * x q) * (√(σ q) * y q)
          = (√(σ q) * √(σ q)) * (x q * y q) := by ring
        _ = σ q * (x q * y q) := by rw [hmm]
    have h2 : (∑ q ∈ T, σ q * (x q * y q)) ^ 2 ≤ A * Bq := by rw [← h1]; exact hcs
    have h3 : ∑ q ∈ T, σ q * (x q * y q) ≤ √(A * Bq) := by
      calc ∑ q ∈ T, σ q * (x q * y q) ≤ |∑ q ∈ T, σ q * (x q * y q)| := le_abs_self _
        _ = √((∑ q ∈ T, σ q * (x q * y q)) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
        _ ≤ √(A * Bq) := Real.sqrt_le_sqrt h2
    rwa [Real.sqrt_mul hA0] at h3
  have hexp : ∑ q ∈ T, σ q * (x q + y q) ^ 2
      = A + 2 * (∑ q ∈ T, σ q * (x q * y q)) + Bq := by
    rw [hA, hB, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ => by ring
  rw [hexp]
  have hkey : A + 2 * (∑ q ∈ T, σ q * (x q * y q)) + Bq ≤ (√A + √Bq) ^ 2 := by
    have h1 : (√A + √Bq) ^ 2 = A + 2 * (√A * √Bq) + Bq := by
      have e1 : √A ^ 2 = A := Real.sq_sqrt hA0
      have e2 : √Bq ^ 2 = Bq := Real.sq_sqrt hB0
      nlinarith [e1, e2]
    rw [h1]; linarith
  calc √(A + 2 * (∑ q ∈ T, σ q * (x q * y q)) + Bq) ≤ √((√A + √Bq) ^ 2) :=
        Real.sqrt_le_sqrt hkey
    _ = √A + √Bq := Real.sqrt_sq (by positivity)

/-- **Minkowski for a finite sum in a weighted `ℓ²`.**  This is the step that the scalar
`RBM.Step2Bootstrap.abs_deriv_softMax_le_affine` cannot perform, and without which the
cardinality factor of appendix B returns. -/
theorem sqrt_wsum_sum_le (T : Finset κ) (S : Finset ι) (σ : κ → ℝ) (hσ : ∀ q ∈ T, 0 ≤ σ q)
    (g : ι → κ → ℝ) :
    √(∑ q ∈ T, σ q * (∑ i ∈ S, g i q) ^ 2) ≤ ∑ i ∈ S, √(∑ q ∈ T, σ q * g i q ^ 2) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert j S hj ih =>
      have hsplit : ∀ q, ∑ i ∈ insert j S, g i q = g j q + ∑ i ∈ S, g i q := fun q => by
        rw [Finset.sum_insert hj]
      have hrw : ∑ q ∈ T, σ q * (∑ i ∈ insert j S, g i q) ^ 2
          = ∑ q ∈ T, σ q * (g j q + ∑ i ∈ S, g i q) ^ 2 :=
        Finset.sum_congr rfl fun q _ => by rw [hsplit q]
      rw [hrw, Finset.sum_insert hj]
      exact (sqrt_wsum_add_le T σ hσ (g j) (fun q => ∑ i ∈ S, g i q)).trans (by gcongr)

/-! #### 8.2 The directional derivatives, against the numerator's own gradient -/

/-- `ρ^{2r}` is `C¹` whenever the numerator is; the even power is what keeps the map smooth
at `f = 0` (`RBM.Gauss.not_bddC2C_norm_div`). -/
theorem contDiff_ratio_pow {f : E → ℂ} (hf : ContDiff ℝ 1 f) (c : ℝ) (r : ℕ) :
    ContDiff ℝ 1 (fun M => (‖f M‖ / c) ^ (2 * r)) := by
  have h : ContDiff ℝ 1 (fun M => (‖f M‖ ^ 2 / c ^ 2) ^ r) :=
    (((hf.norm_sq ℝ).div_const (c ^ 2)).pow r)
  have hfun : (fun M : E => (‖f M‖ / c) ^ (2 * r)) = fun M : E => (‖f M‖ ^ 2 / c ^ 2) ^ r := by
    funext M; rw [pow_mul, div_pow]
  rw [hfun]; exact h

/-- **⭐ The directional derivative of one ratio power.**  Unlike
`RBM.Gauss.norm_fderiv_ratio_pow_le`, the right-hand side carries the numerator's *own*
derivative in the *same* direction, not a uniform constant — this is what allows the
`ℓ²(usedCoord, gvar)` sum to be taken afterwards. -/
theorem abs_fderiv_ratio_pow_apply_le {f : E → ℂ} (hf : ContDiff ℝ 1 f) {c : ℝ} (hc : 0 < c)
    {r : ℕ} (hr : 1 ≤ r) (M B : E) :
    |fderiv ℝ (fun M => (‖f M‖ / c) ^ (2 * r)) M B|
      ≤ ((2 * r : ℕ) : ℝ) * (‖f M‖ / c) ^ (2 * r - 1) * (‖fderiv ℝ f M B‖ / c) := by
  have hc2 : (0 : ℝ) < c ^ 2 := by positivity
  have hd : HasFDerivAt f (fderiv ℝ f M) M := (hf.differentiable one_ne_zero M).hasFDerivAt
  have hns := hd.norm_sq
  have hq : HasFDerivAt (fun x : E => ‖f x‖ ^ 2 / c ^ 2)
      (((c ^ 2)⁻¹ : ℝ) • (2 • (innerSL ℝ (f M)).comp (fderiv ℝ f M))) M := by
    have h := hns.const_smul ((c ^ 2)⁻¹ : ℝ)
    simpa [Pi.smul_def, div_eq_inv_mul, smul_eq_mul] using h
  have hp := hq.pow r
  have hfun : (fun M : E => (‖f M‖ / c) ^ (2 * r)) = fun M : E => (‖f M‖ ^ 2 / c ^ 2) ^ r := by
    funext M; rw [pow_mul, div_pow]
  rw [hfun, hp.fderiv]
  have hval : ((r • (‖f M‖ ^ 2 / c ^ 2) ^ (r - 1)) •
      (((c ^ 2)⁻¹ : ℝ) • (2 • (innerSL ℝ (f M)).comp (fderiv ℝ f M)))) B
      = (r : ℝ) * (‖f M‖ ^ 2 / c ^ 2) ^ (r - 1) *
        ((2 * (inner ℝ (f M) (fderiv ℝ f M B) : ℝ)) / c ^ 2) := by
    simp [nsmul_eq_mul]
    left; field_simp
  rw [hval]
  set ρ : ℝ := ‖f M‖ / c with hρ
  have hρ0 : 0 ≤ ρ := by rw [hρ]; positivity
  have hρ2 : ρ ^ 2 = ‖f M‖ ^ 2 / c ^ 2 := by rw [hρ, div_pow]
  have he1 : (‖f M‖ ^ 2 / c ^ 2) ^ (r - 1) = ρ ^ (2 * r - 2) := by
    rw [← hρ2, ← pow_mul]; congr 1; omega
  have he2 : ρ ^ (2 * r - 2) * ρ = ρ ^ (2 * r - 1) := by
    rw [← pow_succ]; congr 1; omega
  rw [he1]
  have hbound : |(2 * (inner ℝ (f M) (fderiv ℝ f M B) : ℝ)) / c ^ 2|
      ≤ 2 * (‖f M‖ * ‖fderiv ℝ f M B‖) / c ^ 2 := by
    rw [abs_div, abs_of_pos hc2, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    have := abs_real_inner_le_norm (f M) (fderiv ℝ f M B)
    gcongr
  calc |(r : ℝ) * ρ ^ (2 * r - 2) * ((2 * (inner ℝ (f M) (fderiv ℝ f M B) : ℝ)) / c ^ 2)|
      = (r : ℝ) * ρ ^ (2 * r - 2) *
          |(2 * (inner ℝ (f M) (fderiv ℝ f M B) : ℝ)) / c ^ 2| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg r),
          abs_of_nonneg (pow_nonneg hρ0 _)]
    _ ≤ (r : ℝ) * ρ ^ (2 * r - 2) * (2 * (‖f M‖ * ‖fderiv ℝ f M B‖) / c ^ 2) := by
        have h0 : (0:ℝ) ≤ (r : ℝ) * ρ ^ (2 * r - 2) := by positivity
        exact mul_le_mul_of_nonneg_left hbound h0
    _ = ((2 * r : ℕ) : ℝ) * (ρ ^ (2 * r - 2) * ρ) * (‖fderiv ℝ f M B‖ / c) := by
        rw [hρ]; push_cast; field_simp
    _ = ((2 * r : ℕ) : ℝ) * ρ ^ (2 * r - 1) * (‖fderiv ℝ f M B‖ / c) := by rw [he2]

/-- The `c = 1` case: the directional derivative of `‖Ψ‖^{2p}`. -/
theorem abs_fderiv_norm_pow_apply_le {f : E → ℂ} (hf : ContDiff ℝ 1 f) {p : ℕ} (hp : 1 ≤ p)
    (M B : E) :
    |fderiv ℝ (fun M => ‖f M‖ ^ (2 * p)) M B|
      ≤ ((2 * p : ℕ) : ℝ) * ‖f M‖ ^ (2 * p - 1) * ‖fderiv ℝ f M B‖ := by
  have h := abs_fderiv_ratio_pow_apply_le hf (c := 1) one_pos hp M B
  simpa using h

/-- **The directional gradient of `J̃ = Y^{1/(2r)}`**, bounded by the numerators' gradients in
the same direction.  The factor `2r` of the polynomial is cancelled by the outer exponent. -/
theorem abs_fderiv_softMax_apply_le (S : Finset ι) {f : ι → E → ℂ} {c : ι → ℝ} {r : ℕ}
    (hr : 1 ≤ r) (hc : ∀ i ∈ S, 0 < c i) (hf : ∀ i ∈ S, ContDiff ℝ 1 (f i)) (M B : E)
    (hY : 0 < ∑ i ∈ S, (‖f i M‖ / c i) ^ (2 * r)) :
    |fderiv ℝ (fun M => softMax r S (fun i => ‖f i M‖ / c i)) M B|
      ≤ (∑ i ∈ S, (‖f i M‖ / c i) ^ (2 * r)) ^ ((1 : ℝ) / (2 * (r : ℝ)) - 1) *
          ∑ i ∈ S, (‖f i M‖ / c i) ^ (2 * r - 1) * (‖fderiv ℝ (f i) M B‖ / c i) := by
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hn0 : (0 : ℝ) < 2 * (r : ℝ) := by linarith
  set a : ℝ := (1 : ℝ) / (2 * (r : ℝ)) with ha
  set Y : E → ℝ := fun M => ∑ i ∈ S, (‖f i M‖ / c i) ^ (2 * r) with hYdef
  have hdi : ∀ i ∈ S, HasFDerivAt (fun M => (‖f i M‖ / c i) ^ (2 * r))
      (fderiv ℝ (fun M => (‖f i M‖ / c i) ^ (2 * r)) M) M := fun i hi =>
    ((contDiff_ratio_pow (hf i hi) (c i) r).differentiable one_ne_zero M).hasFDerivAt
  have hYd : HasFDerivAt Y (∑ i ∈ S, fderiv ℝ (fun M => (‖f i M‖ / c i) ^ (2 * r)) M) M :=
    HasFDerivAt.fun_sum hdi
  have hJ : HasFDerivAt (fun M => Y M ^ a) ((a * Y M ^ (a - 1)) • fderiv ℝ Y M) M :=
    hYd.fderiv ▸ (hYd.rpow_const (Or.inl hY.ne'))
  have hfun : (fun M : E => softMax r S (fun i => ‖f i M‖ / c i)) = fun M => Y M ^ a := rfl
  rw [hfun, hJ.fderiv]
  have hYa : (0 : ℝ) < Y M ^ (a - 1) := Real.rpow_pos_of_pos hY _
  have ha0 : (0 : ℝ) < a := by rw [ha]; positivity
  have hsum : |fderiv ℝ Y M B|
      ≤ ((2 * r : ℕ) : ℝ) *
        ∑ i ∈ S, (‖f i M‖ / c i) ^ (2 * r - 1) * (‖fderiv ℝ (f i) M B‖ / c i) := by
    rw [hYd.fderiv]
    have hstep : |(∑ i ∈ S, fderiv ℝ (fun M => (‖f i M‖ / c i) ^ (2 * r)) M) B|
        ≤ ∑ i ∈ S, ((2 * r : ℕ) : ℝ) * (‖f i M‖ / c i) ^ (2 * r - 1) *
            (‖fderiv ℝ (f i) M B‖ / c i) := by
      rw [FunLike.coe_sum, Finset.sum_apply]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
      exact abs_fderiv_ratio_pow_apply_le (hf i hi) (hc i hi) hr M B
    refine hstep.trans (le_of_eq ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hcast : ((2 * r : ℕ) : ℝ) * a = 1 := by rw [ha]; push_cast; field_simp
  have hnn : (0 : ℝ) ≤ ∑ i ∈ S,
      (‖f i M‖ / c i) ^ (2 * r - 1) * (‖fderiv ℝ (f i) M B‖ / c i) := by
    refine Finset.sum_nonneg fun i hi => ?_
    have := (hc i hi).le
    positivity
  rw [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, abs_mul,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ a * Y M ^ (a - 1))]
  calc a * Y M ^ (a - 1) * |fderiv ℝ Y M B|
      ≤ a * Y M ^ (a - 1) * (((2 * r : ℕ) : ℝ) *
          ∑ i ∈ S, (‖f i M‖ / c i) ^ (2 * r - 1) * (‖fderiv ℝ (f i) M B‖ / c i)) := by
        exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (((2 * r : ℕ) : ℝ) * a) * (Y M ^ (a - 1) *
          ∑ i ∈ S, (‖f i M‖ / c i) ^ (2 * r - 1) * (‖fderiv ℝ (f i) M B‖ / c i)) := by ring
    _ = Y M ^ (a - 1) *
          ∑ i ∈ S, (‖f i M‖ / c i) ^ (2 * r - 1) * (‖fderiv ℝ (f i) M B‖ / c i) := by
        rw [hcast, one_mul]

end VectorQV

/-! #### 8.3 (S2) on the model's coordinates -/

section S2

variable {d : Dims} {N : ℕ} {ι : Type*}

/-- A real-valued functional, read through `RBM.Gauss.coordD1`. -/
theorem norm_coordD1_ofReal {g : Matrix (d.Idx N) (d.Idx N) ℂ → ℝ}
    {M : Matrix (d.Idx N) (d.Idx N) ℂ} (hg : DifferentiableAt ℝ g M)
    (q : d.Idx N × d.Idx N × Bool) :
    ‖coordD1 d N (fun M => ((g M : ℝ) : ℂ)) M q‖
      = |fderiv ℝ g M (Bmat d N q.1 q.2.1 q.2.2)| := by
  have hfd : fderiv ℝ (fun M => ((g M : ℝ) : ℂ)) M
      = Complex.ofRealCLM.comp (fderiv ℝ g M) :=
    (Complex.ofRealCLM.hasFDerivAt.comp M hg.hasFDerivAt).fderiv
  change ‖fderiv ℝ (fun M => ((g M : ℝ) : ℂ)) M (Bmat d N q.1 q.2.1 q.2.2)‖ = _
  rw [hfd]
  simp [Complex.norm_real, Real.norm_eq_abs]

/-- A coordinatewise comparison of two gradients upgrades to their quadratic-variation
rates. -/
theorem sqrt_quadVar_le_of_apply_le {F G : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}
    {M : Matrix (d.Idx N) (d.Idx N) ℂ} {L : ℝ} (hL : 0 ≤ L)
    (h : ∀ q ∈ usedCoord d N, ‖coordD1 d N F M q‖ ≤ L * ‖coordD1 d N G M q‖) :
    √(quadVar d N F M) ≤ L * √(quadVar d N G M) := by
  have hq : quadVar d N F M ≤ L ^ 2 * quadVar d N G M := by
    rw [quadVar, quadVar, Finset.mul_sum]
    refine Finset.sum_le_sum fun q hq => ?_
    have h1 : ‖coordD1 d N F M q‖ ^ 2 ≤ L ^ 2 * ‖coordD1 d N G M q‖ ^ 2 := by
      have := pow_le_pow_left₀ (norm_nonneg _) (h q hq) 2
      calc ‖coordD1 d N F M q‖ ^ 2 ≤ (L * ‖coordD1 d N G M q‖) ^ 2 := this
        _ = L ^ 2 * ‖coordD1 d N G M q‖ ^ 2 := by ring
    calc ((gvar d (crd d N q) : ℝ)) * ‖coordD1 d N F M q‖ ^ 2
        ≤ ((gvar d (crd d N q) : ℝ)) * (L ^ 2 * ‖coordD1 d N G M q‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h1 (gvar d (crd d N q)).2
      _ = L ^ 2 * (((gvar d (crd d N q) : ℝ)) * ‖coordD1 d N G M q‖ ^ 2) := by ring
  calc √(quadVar d N F M) ≤ √(L ^ 2 * quadVar d N G M) := Real.sqrt_le_sqrt hq
    _ = L * √(quadVar d N G M) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hL]

/-- **⭐⭐ (S2): the vector bound on the quadratic-variation rate of the soft maximum.**

`√(quadVar J̃) ≤ card^{1/(2r)} · max_{i ∈ S} √(quadVar f_i)/c_i`, stated with any upper bound
`K` for the maximum (the maximum itself is the least such `K`).

⚠ The constant `K` is a **quadratic-variation rate of the numerators at the same point `M`**,
not a deterministic derivative bound: substituting the uniform `b₁` of
`RBM.Gauss.BddC2C` here produces a true but useless estimate (V548, appendix B).  The proof
does Minkowski in `ℓ²(usedCoord, gvar)` first (`RBM.Gauss.sqrt_wsum_sum_le`) and Hölder in `i`
second (`RBM.Step2Bootstrap.sum_abs_pow_pred_le`); doing them in the other order is exactly
what costs the factor `card S`. -/
theorem sqrt_quadVar_softMax_le (S : Finset ι)
    {f : ι → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} {c : ι → ℝ} {r : ℕ} {K : ℝ}
    (hr : 1 ≤ r) (hc : ∀ i ∈ S, 0 < c i) (hf : ∀ i ∈ S, ContDiff ℝ 1 (f i))
    (M : Matrix (d.Idx N) (d.Idx N) ℂ)
    (hY : 0 < ∑ i ∈ S, (‖f i M‖ / c i) ^ (2 * r))
    (hK : ∀ i ∈ S, √(quadVar d N (f i) M) / c i ≤ K) :
    √(quadVar d N (fun M => ((softMax r S (fun i => ‖f i M‖ / c i) : ℝ) : ℂ)) M)
      ≤ (S.card : ℝ) ^ ((1 : ℝ) / (2 * (r : ℝ))) * K := by
  classical
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hn0 : (0 : ℝ) < 2 * (r : ℝ) := by linarith
  set a : ℝ := (1 : ℝ) / (2 * (r : ℝ)) with ha
  set Yv : ℝ := ∑ i ∈ S, (‖f i M‖ / c i) ^ (2 * r) with hYv
  have hYa : (0 : ℝ) < Yv ^ (a - 1) := Real.rpow_pos_of_pos hY _
  have hSne : S.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [hYv, h] at hY; simp at hY
  obtain ⟨i₀, hi₀⟩ := hSne
  have hK0 : 0 ≤ K :=
    le_trans (div_nonneg (Real.sqrt_nonneg _) (hc i₀ hi₀).le) (hK i₀ hi₀)
  set w : ι → ℝ := fun i => Yv ^ (a - 1) * (‖f i M‖ / c i) ^ (2 * r - 1) / c i with hw
  have hw0 : ∀ i ∈ S, 0 ≤ w i := by
    intro i hi
    have := (hc i hi).le
    rw [hw]
    positivity
  set g : ι → d.Idx N × d.Idx N × Bool → ℝ :=
    fun i q => w i * ‖coordD1 d N (f i) M q‖ with hg
  have hJd : DifferentiableAt ℝ (fun M => softMax r S (fun i => ‖f i M‖ / c i)) M := by
    have hdi : ∀ i ∈ S, HasFDerivAt (fun M => (‖f i M‖ / c i) ^ (2 * r))
        (fderiv ℝ (fun M => (‖f i M‖ / c i) ^ (2 * r)) M) M := fun i hi =>
      ((contDiff_ratio_pow (hf i hi) (c i) r).differentiable one_ne_zero M).hasFDerivAt
    have hYd : HasFDerivAt (fun M => ∑ i ∈ S, (‖f i M‖ / c i) ^ (2 * r))
        (∑ i ∈ S, fderiv ℝ (fun M => (‖f i M‖ / c i) ^ (2 * r)) M) M :=
      HasFDerivAt.fun_sum hdi
    exact ((hYd.rpow_const (Or.inl hY.ne')).differentiableAt)
  have hpt : ∀ q ∈ usedCoord d N,
      ‖coordD1 d N (fun M => ((softMax r S (fun i => ‖f i M‖ / c i) : ℝ) : ℂ)) M q‖
        ≤ ∑ i ∈ S, g i q := by
    intro q _
    rw [norm_coordD1_ofReal hJd q]
    refine (abs_fderiv_softMax_apply_le S hr hc hf M _ hY).trans (le_of_eq ?_)
    rw [hg, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hw]
    simp only [coordD1]
    ring
  have hquad : quadVar d N (fun M => ((softMax r S (fun i => ‖f i M‖ / c i) : ℝ) : ℂ)) M
      ≤ ∑ q ∈ usedCoord d N, ((gvar d (crd d N q) : ℝ)) * (∑ i ∈ S, g i q) ^ 2 := by
    rw [quadVar]
    refine Finset.sum_le_sum fun q hq => ?_
    refine mul_le_mul_of_nonneg_left ?_ (gvar d (crd d N q)).2
    exact pow_le_pow_left₀ (norm_nonneg _) (hpt q hq) 2
  have hmink := sqrt_wsum_sum_le (usedCoord d N) S (fun q => (gvar d (crd d N q) : ℝ))
    (fun q _ => (gvar d (crd d N q)).2) g
  have hterm : ∀ i ∈ S,
      √(∑ q ∈ usedCoord d N, ((gvar d (crd d N q) : ℝ)) * g i q ^ 2)
        = w i * √(quadVar d N (f i) M) := by
    intro i hi
    have hrw : ∑ q ∈ usedCoord d N, ((gvar d (crd d N q) : ℝ)) * g i q ^ 2
        = w i ^ 2 * quadVar d N (f i) M := by
      rw [quadVar, Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [hg]; ring
    rw [hrw, Real.sqrt_mul (by positivity), Real.sqrt_sq (hw0 i hi)]
  refine le_trans (Real.sqrt_le_sqrt hquad) (le_trans hmink ?_)
  have hstep : ∑ i ∈ S, √(∑ q ∈ usedCoord d N, ((gvar d (crd d N q) : ℝ)) * g i q ^ 2)
      ≤ ∑ i ∈ S, Yv ^ (a - 1) * ((‖f i M‖ / c i) ^ (2 * r - 1) * K) := by
    rw [Finset.sum_congr rfl hterm]
    refine Finset.sum_le_sum fun i hi => ?_
    have hci : (0 : ℝ) < c i := hc i hi
    have h1 : √(quadVar d N (f i) M) / c i ≤ K := hK i hi
    have hpow : (0 : ℝ) ≤ (‖f i M‖ / c i) ^ (2 * r - 1) := by positivity
    have hsplit : w i * √(quadVar d N (f i) M)
        = Yv ^ (a - 1) * (‖f i M‖ / c i) ^ (2 * r - 1) *
          (√(quadVar d N (f i) M) / c i) := by
      rw [hw]; field_simp
    rw [hsplit]
    have h0 : (0 : ℝ) ≤ Yv ^ (a - 1) * (‖f i M‖ / c i) ^ (2 * r - 1) := by positivity
    calc Yv ^ (a - 1) * (‖f i M‖ / c i) ^ (2 * r - 1) * (√(quadVar d N (f i) M) / c i)
        ≤ Yv ^ (a - 1) * (‖f i M‖ / c i) ^ (2 * r - 1) * K :=
          mul_le_mul_of_nonneg_left h1 h0
      _ = Yv ^ (a - 1) * ((‖f i M‖ / c i) ^ (2 * r - 1) * K) := by ring
  refine hstep.trans ?_
  have hcollect : ∑ i ∈ S, Yv ^ (a - 1) * ((‖f i M‖ / c i) ^ (2 * r - 1) * K)
      = Yv ^ (a - 1) * ((∑ i ∈ S, (‖f i M‖ / c i) ^ (2 * r - 1)) * K) := by
    rw [← Finset.mul_sum, ← Finset.sum_mul]
  rw [hcollect]
  have hhold := sum_abs_pow_pred_le (S := S) (ρ := fun i => ‖f i M‖ / c i) hr
  have habs : ∑ i ∈ S, |‖f i M‖ / c i| ^ (2 * r - 1)
      = ∑ i ∈ S, (‖f i M‖ / c i) ^ (2 * r - 1) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [abs_of_nonneg (div_nonneg (norm_nonneg _) (hc i hi).le)]
  rw [habs] at hhold
  calc Yv ^ (a - 1) * ((∑ i ∈ S, (‖f i M‖ / c i) ^ (2 * r - 1)) * K)
      ≤ Yv ^ (a - 1) * (((S.card : ℝ) ^ a * Yv ^ (1 - a)) * K) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hhold hK0) hYa.le
    _ = (Yv ^ (a - 1) * Yv ^ (1 - a)) * ((S.card : ℝ) ^ a * K) := by ring
    _ = (S.card : ℝ) ^ a * K := by
        rw [← Real.rpow_add hY]
        norm_num

end S2

section S5

variable {d : Dims} {N : ℕ} {ι : Type*}

/-- A vanishing differential makes the quadratic-variation rate vanish. -/
theorem quadVar_eq_zero_of_fderiv_eq_zero {F : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}
    {M : Matrix (d.Idx N) (d.Idx N) ℂ} (h : fderiv ℝ F M = 0) : quadVar d N F M = 0 := by
  rw [quadVar]
  refine Finset.sum_eq_zero fun q _ => ?_
  have hz : coordD1 d N F M q = 0 := by
    change fderiv ℝ F M (Bmat d N q.1 q.2.1 q.2.2) = 0
    rw [h]; rfl
  rw [hz]; simp

/-- `‖Ψ‖^{2p}` is `C¹` whenever `Ψ` is. -/
theorem contDiff_norm_pow {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ψ : E → ℂ} (hΨ : ContDiff ℝ 1 Ψ) (p : ℕ) :
    ContDiff ℝ 1 (fun M => ‖Ψ M‖ ^ (2 * p)) := by
  have h := contDiff_ratio_pow hΨ 1 p
  simpa using h

/-- The moment factor's quadratic-variation rate. -/
theorem sqrt_quadVar_norm_pow_le {Ψ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}
    (hΨ : ContDiff ℝ 1 Ψ) {p : ℕ} (hp : 1 ≤ p) (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    √(quadVar d N (fun M => ((‖Ψ M‖ ^ (2 * p) : ℝ) : ℂ)) M)
      ≤ ((2 * p : ℕ) : ℝ) * ‖Ψ M‖ ^ (2 * p - 1) * √(quadVar d N Ψ M) := by
  have hd : DifferentiableAt ℝ (fun M => ‖Ψ M‖ ^ (2 * p)) M :=
    (contDiff_norm_pow hΨ p).differentiable one_ne_zero M
  refine sqrt_quadVar_le_of_apply_le (by positivity) fun q _ => ?_
  rw [norm_coordD1_ofReal hd q]
  exact abs_fderiv_norm_pow_apply_le hΨ hp M _

section Weight

variable {f : ι → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} {c : ι → ℝ} {r p : ℕ} {Θ K : ℝ}

/-- Where the soft maximum vanishes the weight is locally constant `1`, so its differential
vanishes: the configuration `L = K` (`Y = 0`) is **not** excluded by any hypothesis below. -/
theorem fderiv_softW_pow_eq_zero_of_sum_eq_zero (S : Finset ι) (hΘ : 0 < Θ) (hr : 1 ≤ r)
    (hf : ∀ i ∈ S, ContDiff ℝ 1 (f i))
    {M : Matrix (d.Idx N) (d.Idx N) ℂ}
    (hY : ∑ i ∈ S, (‖f i M‖ / c i) ^ (2 * r) = 0) (p : ℕ) :
    fderiv ℝ (fun M => (((softW r S (fun i => ‖f i M‖ / c i) Θ) ^ (2 * p) : ℝ) : ℂ)) M = 0 := by
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hn0 : (0 : ℝ) < 2 * (r : ℝ) := by linarith
  set a : ℝ := (1 : ℝ) / (2 * (r : ℝ)) with ha
  have ha0 : (0 : ℝ) < a := by rw [ha]; positivity
  set Y : Matrix (d.Idx N) (d.Idx N) ℂ → ℝ :=
    fun M => ∑ i ∈ S, (‖f i M‖ / c i) ^ (2 * r) with hYdef
  set σm : Matrix (d.Idx N) (d.Idx N) ℂ → ℝ :=
    fun M => softMax r S (fun i => ‖f i M‖ / c i) with hσdef
  have hYc : ContDiff ℝ 1 Y :=
    ContDiff.sum (fun i hi => contDiff_ratio_pow (hf i hi) (c i) r)
  have hYM : Y M = 0 := hY
  have hσeq : σm M = Y M ^ a := rfl
  have hσ0 : σm M = 0 := by rw [hσeq, hYM, Real.zero_rpow ha0.ne']
  have hcont : ContinuousAt σm M := by
    have h1 : ContinuousAt Y M := hYc.continuous.continuousAt
    have h2 : ContinuousAt (fun y : ℝ => y ^ a) (Y M) :=
      Real.continuousAt_rpow_const _ _ (Or.inr ha0.le)
    exact h2.comp h1
  have hnb : ∀ᶠ M' in nhds M, σm M' < Θ :=
    hcont (Iio_mem_nhds (by rw [hσ0]; exact hΘ))
  have heq : (fun M' => (((softW r S (fun i => ‖f i M'‖ / c i) Θ) ^ (2 * p) : ℝ) : ℂ))
      =ᶠ[nhds M] fun _ => (1 : ℂ) := by
    filter_upwards [hnb] with M' hM'
    rw [softW, cutChi_eq_one ((div_le_one hΘ).2 hM'.le)]
    simp
  rw [heq.fderiv_eq]
  simp

/-- **⭐ The weight's quadratic-variation rate**, from (S2) and `|χ'| ≤ 15/8`. -/
theorem sqrt_quadVar_softW_pow_le (S : Finset ι) (hr : 1 ≤ r) (hp : 1 ≤ p) (hΘ : 0 < Θ)
    (hK0 : 0 ≤ K) (hc : ∀ i ∈ S, 0 < c i) (hf : ∀ i ∈ S, ContDiff ℝ 1 (f i))
    (M : Matrix (d.Idx N) (d.Idx N) ℂ)
    (hK : ∀ i ∈ S, √(quadVar d N (f i) M) / c i ≤ K) :
    √(quadVar d N
        (fun M => (((softW r S (fun i => ‖f i M‖ / c i) Θ) ^ (2 * p) : ℝ) : ℂ)) M)
      ≤ ((2 * p : ℕ) : ℝ) * (softW r S (fun i => ‖f i M‖ / c i) Θ) ^ (2 * p - 1)
          * ((15 / 8) / Θ) * ((S.card : ℝ) ^ ((1 : ℝ) / (2 * (r : ℝ))) * K) := by
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hn0 : (0 : ℝ) < 2 * (r : ℝ) := by linarith
  set a : ℝ := (1 : ℝ) / (2 * (r : ℝ)) with ha
  have ha0 : (0 : ℝ) < a := by rw [ha]; positivity
  set Y : Matrix (d.Idx N) (d.Idx N) ℂ → ℝ :=
    fun M => ∑ i ∈ S, (‖f i M‖ / c i) ^ (2 * r) with hYdef
  set σm : Matrix (d.Idx N) (d.Idx N) ℂ → ℝ :=
    fun M => softMax r S (fun i => ‖f i M‖ / c i) with hσdef
  have hcard : (0 : ℝ) ≤ (S.card : ℝ) ^ a := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hrhs0 : (0 : ℝ) ≤ ((2 * p : ℕ) : ℝ) *
      (softW r S (fun i => ‖f i M‖ / c i) Θ) ^ (2 * p - 1) * ((15 / 8) / Θ) *
      ((S.card : ℝ) ^ a * K) := by
    have h1 : (0 : ℝ) ≤ softW r S (fun i => ‖f i M‖ / c i) Θ := softW_nonneg _ _ _ _
    have h2 : (0 : ℝ) ≤ (15 / 8) / Θ := by positivity
    positivity
  rcases eq_or_lt_of_le (sum_even_pow_nonneg S (fun i => ‖f i M‖ / c i) r) with hY0 | hY
  · -- `Y M = 0`: the weight is locally constant `1`.
    have hzero := fderiv_softW_pow_eq_zero_of_sum_eq_zero S hΘ hr hf hY0.symm p
    rw [quadVar_eq_zero_of_fderiv_eq_zero hzero, Real.sqrt_zero]
    exact hrhs0
  · -- `Y M > 0`: the chain rule.
    have hYc : ContDiff ℝ 1 Y :=
      ContDiff.sum (fun i hi => contDiff_ratio_pow (hf i hi) (c i) r)
    have hd : HasFDerivAt Y (fderiv ℝ Y M) M :=
      (hYc.differentiable one_ne_zero M).hasFDerivAt
    have hσd : HasFDerivAt σm ((a * Y M ^ (a - 1)) • fderiv ℝ Y M) M :=
      hd.rpow_const (Or.inl hY.ne')
    have hdiv : HasFDerivAt (fun M' => σm M' / Θ)
        (Θ⁻¹ • ((a * Y M ^ (a - 1)) • fderiv ℝ Y M)) M := by
      have := hσd.const_mul (Θ⁻¹ : ℝ)
      simpa [div_eq_inv_mul] using this
    have hchain := (hasDerivAt_cutChi (σm M / Θ)).comp_hasFDerivAt M hdiv
    have hsw : HasFDerivAt (fun M' => softW r S (fun i => ‖f i M'‖ / c i) Θ)
        (cutChiD (σm M / Θ) • (Θ⁻¹ • ((a * Y M ^ (a - 1)) • fderiv ℝ Y M))) M := hchain
    have hWp := hsw.pow (2 * p)
    have hJd : DifferentiableAt ℝ σm M := hσd.differentiableAt
    set L : ℝ := ((2 * p : ℕ) : ℝ) * (softW r S (fun i => ‖f i M‖ / c i) Θ) ^ (2 * p - 1)
        * ((15 / 8) / Θ) with hL
    have hsw0 : (0 : ℝ) ≤ softW r S (fun i => ‖f i M‖ / c i) Θ := softW_nonneg _ _ _ _
    have hL0 : (0 : ℝ) ≤ L := by
      rw [hL]
      have h2 : (0 : ℝ) ≤ (15 / 8) / Θ := by positivity
      positivity
    have hWd : DifferentiableAt ℝ
        (fun M' => (softW r S (fun i => ‖f i M'‖ / c i) Θ) ^ (2 * p)) M := hWp.differentiableAt
    have hWfd : ∀ B, |fderiv ℝ (fun M' => (softW r S (fun i => ‖f i M'‖ / c i) Θ) ^ (2 * p)) M B|
        ≤ L * |fderiv ℝ σm M B| := by
      intro B
      have hval : fderiv ℝ (fun M' => (softW r S (fun i => ‖f i M'‖ / c i) Θ) ^ (2 * p)) M B
          = ((2 * p : ℕ) : ℝ) * (softW r S (fun i => ‖f i M‖ / c i) Θ) ^ (2 * p - 1)
            * (cutChiD (σm M / Θ) * (Θ⁻¹ * fderiv ℝ σm M B)) := by
        rw [hWp.fderiv, hσd.fderiv]
        simp [nsmul_eq_mul]
      rw [hval]
      simp only [abs_mul]
      rw [Nat.abs_cast, abs_of_nonneg (pow_nonneg hsw0 _), abs_of_pos (inv_pos.2 hΘ)]
      have hchi := abs_cutChiD_le (σm M / Θ)
      have h0 : (0 : ℝ) ≤ ((2 * p : ℕ) : ℝ) *
          (softW r S (fun i => ‖f i M‖ / c i) Θ) ^ (2 * p - 1) := by positivity
      calc ((2 * p : ℕ) : ℝ) * (softW r S (fun i => ‖f i M‖ / c i) Θ) ^ (2 * p - 1) *
            (|cutChiD (σm M / Θ)| * (Θ⁻¹ * |fderiv ℝ σm M B|))
          ≤ ((2 * p : ℕ) : ℝ) * (softW r S (fun i => ‖f i M‖ / c i) Θ) ^ (2 * p - 1) *
            ((15 / 8) * (Θ⁻¹ * |fderiv ℝ σm M B|)) := by
            refine mul_le_mul_of_nonneg_left ?_ h0
            exact mul_le_mul_of_nonneg_right hchi (by positivity)
        _ = L * |fderiv ℝ σm M B| := by rw [hL, div_eq_mul_inv]; ring
    have hcmp : ∀ q ∈ usedCoord d N,
        ‖coordD1 d N
            (fun M => (((softW r S (fun i => ‖f i M‖ / c i) Θ) ^ (2 * p) : ℝ) : ℂ)) M q‖
          ≤ L * ‖coordD1 d N (fun M => ((σm M : ℝ) : ℂ)) M q‖ := by
      intro q _
      rw [norm_coordD1_ofReal hWd q, norm_coordD1_ofReal hJd q]
      exact hWfd _
    have hstep := sqrt_quadVar_le_of_apply_le (F := fun M =>
        (((softW r S (fun i => ‖f i M‖ / c i) Θ) ^ (2 * p) : ℝ) : ℂ))
      (G := fun M => ((σm M : ℝ) : ℂ)) hL0 hcmp
    have hS2 := sqrt_quadVar_softMax_le S hr hc hf M hY hK
    refine hstep.trans ?_
    calc L * √(quadVar d N (fun M => ((σm M : ℝ) : ℂ)) M)
        ≤ L * ((S.card : ℝ) ^ a * K) := mul_le_mul_of_nonneg_left hS2 hL0
      _ = ((2 * p : ℕ) : ℝ) * (softW r S (fun i => ‖f i M‖ / c i) Θ) ^ (2 * p - 1)
            * ((15 / 8) / Θ) * ((S.card : ℝ) ^ a * K) := by rw [hL]

/-- **The `1_{S′}` of (S5)**: off the transition band `Θ ≤ J̃ ≤ 2Θ` the weight's
quadratic-variation rate vanishes, because the chain rule's factor is `χ'(J̃/Θ)`
(`RBM.Cutoff.cutChiD_eq_zero_left` / `RBM.Cutoff.cutChiD_eq_zero_right`).  The band is not
empty: `J̃` is continuous and `RBM.Gauss.softRootProfile_ne_const` shows the cutoff really
cuts. -/
theorem quadVar_softW_pow_eq_zero_of_outside_band (S : Finset ι) (hΘ : 0 < Θ) (hr : 1 ≤ r)
    (hf : ∀ i ∈ S, ContDiff ℝ 1 (f i)) {M : Matrix (d.Idx N) (d.Idx N) ℂ}
    (hband : softMax r S (fun i => ‖f i M‖ / c i) ≤ Θ ∨
      2 * Θ ≤ softMax r S (fun i => ‖f i M‖ / c i)) (p : ℕ) :
    quadVar d N
        (fun M => (((softW r S (fun i => ‖f i M‖ / c i) Θ) ^ (2 * p) : ℝ) : ℂ)) M = 0 := by
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hn0 : (0 : ℝ) < 2 * (r : ℝ) := by linarith
  set a : ℝ := (1 : ℝ) / (2 * (r : ℝ)) with ha
  set Y : Matrix (d.Idx N) (d.Idx N) ℂ → ℝ :=
    fun M => ∑ i ∈ S, (‖f i M‖ / c i) ^ (2 * r) with hYdef
  set σm : Matrix (d.Idx N) (d.Idx N) ℂ → ℝ :=
    fun M => softMax r S (fun i => ‖f i M‖ / c i) with hσdef
  refine quadVar_eq_zero_of_fderiv_eq_zero ?_
  rcases eq_or_lt_of_le (sum_even_pow_nonneg S (fun i => ‖f i M‖ / c i) r) with hY0 | hY
  · exact fderiv_softW_pow_eq_zero_of_sum_eq_zero S hΘ hr hf hY0.symm p
  · have hYc : ContDiff ℝ 1 Y :=
      ContDiff.sum (fun i hi => contDiff_ratio_pow (hf i hi) (c i) r)
    have hd : HasFDerivAt Y (fderiv ℝ Y M) M :=
      (hYc.differentiable one_ne_zero M).hasFDerivAt
    have hσd : HasFDerivAt σm ((a * Y M ^ (a - 1)) • fderiv ℝ Y M) M :=
      hd.rpow_const (Or.inl hY.ne')
    have hdiv : HasFDerivAt (fun M' => σm M' / Θ)
        (Θ⁻¹ • ((a * Y M ^ (a - 1)) • fderiv ℝ Y M)) M := by
      have := hσd.const_mul (Θ⁻¹ : ℝ)
      simpa [div_eq_inv_mul] using this
    have hchain := (hasDerivAt_cutChi (σm M / Θ)).comp_hasFDerivAt M hdiv
    have hsw : HasFDerivAt (fun M' => softW r S (fun i => ‖f i M'‖ / c i) Θ)
        (cutChiD (σm M / Θ) • (Θ⁻¹ • ((a * Y M ^ (a - 1)) • fderiv ℝ Y M))) M := hchain
    have hchi0 : cutChiD (σm M / Θ) = 0 := by
      rcases hband with h | h
      · exact cutChiD_eq_zero_left ((div_le_one hΘ).2 h)
      · refine cutChiD_eq_zero_right ?_
        rw [le_div_iff₀ hΘ]
        linarith
    have hWp := hsw.pow (2 * p)
    have hofr : HasFDerivAt
        (fun M' => (((softW r S (fun i => ‖f i M'‖ / c i) Θ) ^ (2 * p) : ℝ) : ℂ))
        (Complex.ofRealCLM.comp
          (((2 * p) • (softW r S (fun i => ‖f i M‖ / c i) Θ) ^ (2 * p - 1)) •
            (cutChiD (σm M / Θ) • (Θ⁻¹ • ((a * Y M ^ (a - 1)) • fderiv ℝ Y M))))) M :=
      Complex.ofRealCLM.hasFDerivAt.comp M hWp
    rw [hofr.fderiv, hchi0]
    simp

end Weight

/-! #### 8.4 (S5): the cross term -/

section Cross

variable {f : ι → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} {c : ι → ℝ} {r p : ℕ} {Θ K : ℝ}

/-- **⭐⭐ (S5): the cross term's pointwise bound.**

`∑_q gvar q · ‖∂_q W‖ · ‖∂_q |Ψ|^{2p}‖ ≤ (2p)² · (W|Ψ|^{2p})^{1−1/(2p)} · (15/8)/Θ ·
card^{1/(2r)} · K · √(quadVar Ψ)`, where `W = χ(J̃/Θ)^{2p}` and
`(W|Ψ|^{2p})^{1−1/(2p)} = χ(J̃/Θ)^{2p−1}·‖Ψ‖^{2p−1}` is written in the natural-power form.

**Both gradients are `RBM.Gauss.coordD1 d N · M q` at the same `M`.**  `K` is the random
same-time rate of (S2), never a deterministic derivative bound; and
`RBM.Gauss.quadVar_softW_pow_eq_zero_of_outside_band` supplies the `1_{S′}` factor. -/
theorem sum_gvar_crossTerm_le (S : Finset ι) {Ψ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}
    (hr : 1 ≤ r) (hp : 1 ≤ p) (hΘ : 0 < Θ) (hK0 : 0 ≤ K) (hc : ∀ i ∈ S, 0 < c i)
    (hf : ∀ i ∈ S, ContDiff ℝ 1 (f i)) (hΨ : ContDiff ℝ 1 Ψ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ)
    (hK : ∀ i ∈ S, √(quadVar d N (f i) M) / c i ≤ K) :
    ∑ q ∈ usedCoord d N, (gvar d (crd d N q) : ℝ) *
        (‖coordD1 d N
            (fun M => (((softW r S (fun i => ‖f i M‖ / c i) Θ) ^ (2 * p) : ℝ) : ℂ)) M q‖
          * ‖coordD1 d N (fun M => ((‖Ψ M‖ ^ (2 * p) : ℝ) : ℂ)) M q‖)
      ≤ (((2 * p : ℕ) : ℝ) * ((2 * p : ℕ) : ℝ))
          * ((softW r S (fun i => ‖f i M‖ / c i) Θ) ^ (2 * p - 1) * ‖Ψ M‖ ^ (2 * p - 1))
          * (((15 / 8) / Θ) * ((S.card : ℝ) ^ ((1 : ℝ) / (2 * (r : ℝ))) * K))
          * √(quadVar d N Ψ M) := by
  refine (Step2Bootstrap.sum_gvar_mul_le_sqrt_quadVar d N _ _ M).trans ?_
  have h1 := sqrt_quadVar_softW_pow_le S hr hp hΘ hK0 hc hf M hK
  have h2 := sqrt_quadVar_norm_pow_le hΨ hp M
  have hsw0 : (0 : ℝ) ≤ softW r S (fun i => ‖f i M‖ / c i) Θ := softW_nonneg _ _ _ _
  have hcard : (0 : ℝ) ≤ (S.card : ℝ) ^ ((1 : ℝ) / (2 * (r : ℝ))) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hb1 : (0 : ℝ) ≤ ((2 * p : ℕ) : ℝ) *
      (softW r S (fun i => ‖f i M‖ / c i) Θ) ^ (2 * p - 1) * ((15 / 8) / Θ) *
      ((S.card : ℝ) ^ ((1 : ℝ) / (2 * (r : ℝ))) * K) := by
    have h2' : (0 : ℝ) ≤ (15 / 8) / Θ := by positivity
    positivity
  calc √(quadVar d N
        (fun M => (((softW r S (fun i => ‖f i M‖ / c i) Θ) ^ (2 * p) : ℝ) : ℂ)) M) *
        √(quadVar d N (fun M => ((‖Ψ M‖ ^ (2 * p) : ℝ) : ℂ)) M)
      ≤ (((2 * p : ℕ) : ℝ) * (softW r S (fun i => ‖f i M‖ / c i) Θ) ^ (2 * p - 1)
            * ((15 / 8) / Θ) * ((S.card : ℝ) ^ ((1 : ℝ) / (2 * (r : ℝ))) * K)) *
          (((2 * p : ℕ) : ℝ) * ‖Ψ M‖ ^ (2 * p - 1) * √(quadVar d N Ψ M)) :=
        mul_le_mul h1 h2 (Real.sqrt_nonneg _) hb1
    _ = (((2 * p : ℕ) : ℝ) * ((2 * p : ℕ) : ℝ))
          * ((softW r S (fun i => ‖f i M‖ / c i) Θ) ^ (2 * p - 1) * ‖Ψ M‖ ^ (2 * p - 1))
          * (((15 / 8) / Θ) * ((S.card : ℝ) ^ ((1 : ℝ) / (2 * (r : ℝ))) * K))
          * √(quadVar d N Ψ M) := by ring

end Cross

end S5

/-! ### 9. Compiled satisfiability witnesses -/

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


/-- The `(+,−)` loop error of (5.29) on `RBM.Gauss.Dims.exampleGrow`, read as a function of the
matrix: the numerator family route (A′) feeds to (S2)/(S5). -/
noncomputable def satLk (N : ℕ) (a : LoopArg (Dims.exampleGrow.L N) 2) :
    Matrix (Dims.exampleGrow.Idx N) (Dims.exampleGrow.Idx N) ℂ → ℂ :=
  fun M => loopObs Dims.exampleGrow N (zt 0 (1 / 2))
      (LoopData.idx ((Step2.sigPM, a) : LoopData (Dims.exampleGrow.L N) 2)) M
    - (band Dims.exampleGrow).Kval 0 N (1 / 2)
        (LoopData.idx ((Step2.sigPM, a) : LoopData (Dims.exampleGrow.L N) 2))

/-- Constants for the whole family at once: the loop length is `2` for every `a`, so
`RBM.Gauss.bddC2C_loopObs_sub` gives one triple that works uniformly. -/
theorem exists_bddC2C_satLk (N : ℕ) :
    ∃ b₁ : ℝ, 0 ≤ b₁ ∧
      ∀ a : LoopArg (Dims.exampleGrow.L N) 2, ∃ b₀ b₂ : ℝ, BddC2C (satLk N a) b₀ b₁ b₂ := by
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
  have hbdd : ∀ a : LoopArg (Dims.exampleGrow.L N) 2, BddC2C (satLk N a) _ _ _ := fun a =>
    bddC2C_loopObs_sub (d := Dims.exampleGrow) (N := N) hz hη hzη hBa hBb hBc
      (LoopData.idx_wf ((Step2.sigPM, a) : LoopData (Dims.exampleGrow.L N) 2))
      ((band Dims.exampleGrow).Kval 0 N (1 / 2)
        (LoopData.idx ((Step2.sigPM, a) : LoopData (Dims.exampleGrow.L N) 2)))
  have hlen : ∀ a : LoopArg (Dims.exampleGrow.L N) 2,
      (LoopData.idx ((Step2.sigPM, a) : LoopData (Dims.exampleGrow.L N) 2)).a.length = 2 :=
    fun a => LoopData.idx_length _
  refine ⟨(Fintype.card (Dims.exampleGrow.Idx N) : ℝ) *
      (((2 : ℕ) : ℝ) * (2 * (1 + (etaT 0 (1 / 2))⁻¹) ^ 3) ^ (2 : ℕ)) + 0, by positivity,
    fun a => ?_⟩
  have h := hbdd a
  rw [hlen a] at h
  exact ⟨_, _, h⟩

/-- **⭐⭐ A compiled satisfiability witness for (S2) and (S5).**

Every hypothesis of `RBM.Gauss.sum_gvar_crossTerm_le` holds simultaneously on the concrete
model `RBM.Gauss.Dims.exampleGrow`, at the genuine two-edge `(+,−)` loop family of (5.29), for
**every** `r, p ≥ 1`, every `Θ > 0` and every matrix `M` — in particular at `L = K`, where
`Y = 0`: `RBM.Gauss.sum_gvar_crossTerm_le` needs no positivity hypothesis on `Y`, because
`RBM.Gauss.fderiv_softW_pow_eq_zero_of_sum_eq_zero` disposes of that point.

The witness's `K` is a crude deterministic majorant (`b₁ √(coordWeight)`), enough to show the
hypotheses are jointly satisfiable; the `K` the argument is *meant* to be used with is the
random same-time rate of (S3), `RBM.EarlyQVRate.quadVar_lkFun_le_ee_sym`. -/
theorem sat_sum_gvar_crossTerm_le (N : ℕ) {r p : ℕ} (hr : 1 ≤ r) (hp : 1 ≤ p)
    {Θ : ℝ} (hΘ : 0 < Θ) (a₀ : LoopArg (Dims.exampleGrow.L N) 2)
    (M : Matrix (Dims.exampleGrow.Idx N) (Dims.exampleGrow.Idx N) ℂ) :
    ∃ K : ℝ, 0 ≤ K ∧
      (∀ a ∈ (Finset.univ : Finset (LoopArg (Dims.exampleGrow.L N) 2)),
          √(quadVar Dims.exampleGrow N (satLk N a) M) / 1 ≤ K) ∧
      ∑ q ∈ usedCoord Dims.exampleGrow N,
          (gvar Dims.exampleGrow (crd Dims.exampleGrow N q) : ℝ) *
            (‖coordD1 Dims.exampleGrow N (fun M =>
                (((softW r (Finset.univ : Finset (LoopArg (Dims.exampleGrow.L N) 2))
                    (fun a => ‖satLk N a M‖ / 1) Θ) ^ (2 * p) : ℝ) : ℂ)) M q‖
              * ‖coordD1 Dims.exampleGrow N
                  (fun M => ((‖satLk N a₀ M‖ ^ (2 * p) : ℝ) : ℂ)) M q‖)
        ≤ (((2 * p : ℕ) : ℝ) * ((2 * p : ℕ) : ℝ))
            * ((softW r (Finset.univ : Finset (LoopArg (Dims.exampleGrow.L N) 2))
                  (fun a => ‖satLk N a M‖ / 1) Θ) ^ (2 * p - 1)
                * ‖satLk N a₀ M‖ ^ (2 * p - 1))
            * (((15 / 8) / Θ) *
                (((Finset.univ : Finset (LoopArg (Dims.exampleGrow.L N) 2)).card : ℝ)
                  ^ ((1 : ℝ) / (2 * (r : ℝ))) * K))
            * √(quadVar Dims.exampleGrow N (satLk N a₀) M) := by
  obtain ⟨b₁, hb₁, hbdd⟩ := exists_bddC2C_satLk N
  refine ⟨b₁ * √(coordWeight Dims.exampleGrow N), by positivity, ?_, ?_⟩
  · intro a _
    rw [div_one]
    obtain ⟨_, _, hba⟩ := hbdd a
    have hq := quadVar_le_of_bddC2C hba M
    calc √(quadVar Dims.exampleGrow N (satLk N a) M)
        ≤ √(b₁ ^ 2 * coordWeight Dims.exampleGrow N) := Real.sqrt_le_sqrt hq
      _ = b₁ * √(coordWeight Dims.exampleGrow N) := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hb₁]
  · have hcd : ∀ a : LoopArg (Dims.exampleGrow.L N) 2, ContDiff ℝ 1 (satLk N a) := by
      intro a
      obtain ⟨_, _, hba⟩ := hbdd a
      exact hba.contDiff.of_le (by norm_num)
    refine sum_gvar_crossTerm_le _ hr hp hΘ (by positivity) (fun a _ => one_pos)
      (fun a _ => hcd a) (hcd a₀) M (fun a _ => ?_)
    rw [div_one]
    obtain ⟨_, _, hba⟩ := hbdd a
    have hq := quadVar_le_of_bddC2C hba M
    calc √(quadVar Dims.exampleGrow N (satLk N a) M)
        ≤ √(b₁ ^ 2 * coordWeight Dims.exampleGrow N) := Real.sqrt_le_sqrt hq
      _ = b₁ * √(coordWeight Dims.exampleGrow N) := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hb₁]

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

   **Superseded (T265, after the V548 ruling).**  The main estimate no longer goes through the
   global `C²` mean-value closure, so `∇²χ` does not occur in it at all: the Stein identity
   (★) lets `∇²` act only on the resolvent factor.  §5–§6 above are kept as regularity tools;
   §8 is the route actually used.

**T265a** (§5.2–§5.3, the vector bound (S2) and the cross term (S5) of the Stein route).

1. *(S2) is stated with an upper bound `K` in place of the maximum.*  The referee's statement
   is `√(quadVar J̃) ≤ card^{1/(2r)}·max_{i∈S} √(quadVar f_i)/c_i`;
   `RBM.Gauss.sqrt_quadVar_softMax_le` quantifies over any `K` with
   `√(quadVar f_i)/c_i ≤ K` for all `i ∈ S`.  The maximum is the least such `K`, so the two
   are equivalent, and the `K`-form is what the caller (which carries a `≺`-type bound, not a
   pointwise maximum) can supply.  No paper change.  No renumbering.
2. *(S5) writes `χ(J̃/Θ)^{2p-1}·‖Ψ‖^{2p-1}` where the referee writes
   `(W|Ψ|^{2p})^{1-1/(2p)}`.*  The two agree because both bases are non-negative; the
   natural-power form avoids an `rpow`/`pow` conversion in every downstream call.  Likewise
   the indicator `1_{S′}` is not a multiplicative factor of
   `RBM.Gauss.sum_gvar_crossTerm_le` but a separate statement,
   `RBM.Gauss.quadVar_softW_pow_eq_zero_of_outside_band`, which says the left-hand side is
   `0` off the band; multiplying the two gives the referee's shape.  No paper change.  No
   renumbering.
3. *The scalars `(2√u)^{-1}` and `√(u_j/u)` of (S5) are not in the Lean statement.*  Every
   statement of §8 is a pointwise inequality at one matrix `M`, with **both** gradients taken
   as `RBM.Gauss.coordD1 d N · M q` at that same `M`.  The rescaling `M ↦ f_i(√(u_j/u)·M)`
   that this forces on the earlier-time loops, and the constants `√u_j ≤ 1` and `u^{-1/2}` its
   `coordD1` produces, are the caller's: they belong to (S3) and to the time integral (S6)
   respectively.  Nothing here mixes two matrix variables.  No paper change.  No renumbering.
-/
