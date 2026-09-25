/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.GridOneStep
import RBM1D.Gauss.MomentGronwall

/-!
# T1490 — one-step conditional variance (the discrete (5.25))

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*; discrete-grid preparation for the true-path pilot A5,
`docs/claude-team/pilot-P4P5-paper.md` §4: the conditional variance of one grid increment is
`Δ ×` the quadratic-variation integrand of (5.25), `RBM.Gauss.quadVar`, up to `O(Δ^{3/2})`.

## Main results

* `RBM.Gauss.TestFun.normSq` — `‖Φ‖²` (read as a `ℂ`-valued function via
  `fun A => ((‖Φ A‖^2 : ℝ) : ℂ)`) is again a `TestFun` whenever `Φ` is, with constants
  inherited from `TestFun.of_bddC2`/`bddC2_momentFun` (`RBM1D/Gauss/MomentGronwall.lean`)
  applied to `momentFun Φ 1`. This is Step 0 (b) of the ticket.
* `RBM.Gauss.Grid.genPt_normSq` (**T1**) — the chain rule for `|Φ|²` against `coordD2`, read
  off through the generator: `genPt d N (‖Φ‖²) M = 2 · Re(conj(Φ M) · genPt d N Φ M) +
  quadVar d N Φ M`. The route is `coordD2_momentFun_ofReal` specialised at `p = 1` (where the
  `(p-1)` coefficient of the `genMomentPt_le` inequality vanishes identically, turning that
  inequality into an *equality*), combined with `ofReal_genMomentPt` and
  `sum_gvar_re_coordD2` (all from `MomentGronwall.lean`), plus the observation that
  `RBM.Gauss.Grid.genPt` and `RBM.Gauss.genD` are literally the same sum (`1/2 = 2⁻¹`).
* `RBM.Gauss.Grid.oneStep_var_le` (**T2**) — for a Hermitian `M`, `Δ ≥ 0`, `TestFun d N Φ`,
  Lipschitz hypotheses on `genPt d N Φ` (constant `Λ₁`) and on `genPt d N (‖Φ‖²)` (constant
  `Λ₂`), and global bounds `‖Φ‖ ≤ B`, `‖genPt d N Φ‖ ≤ G`: writing
  `Var := ∫ ‖Φ (M + √Δ X) − ∫ Φ (M + √Δ X)‖² dP`,
  `|Var − Δ · quadVar d N Φ M| ≤ C_var · (Δ^{3/2} + Δ²)`
  with `C_var` an explicit expression in `Λ₁, Λ₂, B, G, K := ∫‖Xmat‖`, written out in the
  statement:
  `C_var = (2/3)·Λ₂·K + (4/3)·B·Λ₁·K + 2·G² + 2·((2/3)·Λ₁·K)² + 4·B²`.
  Route: `Var = E‖Φ‖² − ‖EΦ‖²` (`integral_normSq_sub_eq`, a general variance identity);
  apply `oneStep_error_le` (T1486/T3) to `Φ` (giving an error `e₁`, `‖e₁‖ ≤ r₁ := (2/3)Λ₁Δ^{3/2}K`)
  and to `‖Φ‖²` (error `e₂`, `‖e₂‖ ≤ r₂ := (2/3)Λ₂Δ^{3/2}K`); expand
  `‖Φ M + Δ·genPt Φ M + e₁‖²` using `genPt_normSq` to identify the leading term as
  `Δ·quadVar d N Φ M`. What remains is `e₂.re − 2·Re(conj(Φ M)·e₁) − ‖S‖²` where
  `S := Δ·genPt Φ M + e₁ = μ − Φ M` (`μ := ∫ Φ(M+√ΔX)`). Bounding `‖S‖²` needs **two** global
  bounds on `S`, combined by a case split at `Δ = 1` (this is the one place the ticket's
  suggested "expand and bound" route is not literally sufficient: a single triangle-inequality
  bound on `‖S‖²` produces a `Δ^{5/2}`/`Δ³` cross term that is *not* dominated by
  `C·(Δ^{3/2}+Δ²)` for large `Δ` with a `Δ`-independent `C`):
  - for `Δ ≤ 1`: `‖S‖ ≤ Δ·G + r₁`, so `‖S‖² ≤ 2Δ²G² + 2r₁² ≤ 2Δ²G² + 2r₁'²·Δ²` (using
    `Δ³ ≤ Δ²` for `Δ ≤ 1`, where `r₁ = r₁'·Δ^{3/2}`, `r₁' := (2/3)Λ₁K`);
  - for `Δ ≥ 1`: `‖S‖ = ‖μ − Φ M‖ ≤ ‖μ‖ + ‖Φ M‖ ≤ 2B` (boundedness alone, no Lipschitz), so
    `‖S‖² ≤ 4B² ≤ 4B²Δ²` (using `1 ≤ Δ²` for `Δ ≥ 1`).
  Both bounds are `≤ (2G² + 2r₁'²)(Δ^{3/2}+Δ²)` resp. `4B²(Δ^{3/2}+Δ²)`, so their sum
  `2G² + 2r₁'² + 4B²` is a `Δ`-independent constant that works for *all* `Δ ≥ 0`; this is the
  origin of the `2G² + 2((2/3)Λ₁K)² + 4B²` piece of `C_var`.

## Step 0 checks (read-only, recorded here per the ticket)

(a) The merged statements of `RBM.Gauss.Grid.oneStep_error_le` and `RBM.Gauss.Grid.genPt`
(T1486, `RBM1D/Gauss/GridOneStep.lean:195/323`): `genPt` is `(1/2 : ℝ) • ∑ p ∈ usedCoord,
gvar p • coordD2 Φ A p`, exactly the same formula (up to `1/2 = 2⁻¹`) as `RBM.Gauss.genD`
(`RBM1D/Gauss/MomentGronwall.lean:547`); `oneStep_error_le` holds for **every** `Δ ≥ 0`, with
no upper bound on `Δ` — this is exactly what forces the case split above.

(b) `TestFun` is `ℂ`-valued in `RBM.Gauss.Generator`; `fun A => ((‖Φ A‖^2 : ℝ) : ℂ)` is a
`TestFun` for `TestFun d N Φ`: `TestFun.normSq` below proves this, reusing
`RBM.Gauss.TestFun.of_bddC2`/`RBM.Gauss.bddC2_momentFun` (`MomentGronwall.lean:840/976`) applied
to `p = 1`, since `RBM.Gauss.TestFun` and `RBM.Gauss.BddC2` have literally the same three global
bounds (only the ambient normed space differs, and `Matrix (d.Idx N) (d.Idx N) ℂ` is one), and
`RBM.Gauss.momentFun Φ 1 = fun A => ((‖Φ A‖^2 : ℝ) : ℂ)` (`momentFun_eq`).

(c) `coordD1`, `coordD2` (`RBM1D/Gauss/Generator.lean:592/597`) are the first/second directional
derivatives of `Φ` along the fixed direction `Bmat p`; `RBM.Gauss.coordD2_momentFun_ofReal`
(`MomentGronwall.lean:501`) computes `coordD2 (momentFun F p)` in terms of `coordD1 F`,
`coordD2 F`; at `p = 1` its `(p-1 : ℕ) = 0` coefficient kills the term that costs
`genMomentPt_le` its inequality (bounding `Re(F̄∂_αF)²` by `‖F‖²‖∂_αF‖²`), so the `p = 1`
specialisation is an *identity*, not merely a bound — this is what T1 needs and what makes T1
provable without any additional hypothesis.

## Deviations from the paper (for `docs/paper-deltas.md`)

None beyond the ones already recorded for `RBM.Gauss.Grid.oneStep_error_le` (T1486) and for
`RBM.Gauss.secondOrder_eq_quadVar`/`TestFun`'s global bounds (T71/T72); this file only combines
those with elementary real/complex algebra (variance identity, case split at `Δ = 1`).
-/

namespace RBM.Gauss

open MeasureTheory Filter
open scoped Matrix.Norms.L2Operator NNReal

/-! ### Step 0 (b): `‖Φ‖²` is again a `TestFun` -/

section NormSqTestFun

variable {d : Dims} {N : ℕ} {Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}

/-- **Step 0 (b).** `‖Φ‖²`, read as the `ℂ`-valued function `fun A => ((‖Φ A‖^2:ℝ):ℂ)`, is a
`TestFun` whenever `Φ` is: it is `momentFun Φ 1` (`momentFun_eq`), and `TestFun` is inherited by
`momentFun` from the (identical) hypotheses of `BddC2` (`TestFun.of_bddC2`). -/
theorem TestFun.normSq (h : TestFun d N Φ) :
    TestFun d N (fun A => ((‖Φ A‖ ^ 2 : ℝ) : ℂ)) := by
  have hb : BddC2 Φ := ⟨h.contDiff, h.bdd₀, h.bdd₁, h.bdd₂⟩
  have h1 := TestFun.of_bddC2 hb 1
  have heq : (fun A => ((‖Φ A‖ ^ 2 : ℝ) : ℂ)) = momentFun Φ 1 := by
    funext A
    rw [momentFun_eq]
  rwa [heq]

end NormSqTestFun

namespace Grid

variable {d : Dims} {N : ℕ} {Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}

/-! ### T1: the generator of `‖Φ‖²` -/

/-- **T1.** `RBM.Gauss.Grid.genPt_normSq`: the chain rule for `|Φ|²` against `coordD2`, read off
through the generator `genPt`. -/
theorem genPt_normSq (h : TestFun d N Φ) (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    genPt d N (fun A => ((‖Φ A‖ ^ 2 : ℝ) : ℂ)) M
      = ((2 * ((starRingEnd ℂ) (Φ M) * genPt d N Φ M).re + quadVar d N Φ M : ℝ) : ℂ) := by
  have heq : (fun A => ((‖Φ A‖ ^ 2 : ℝ) : ℂ)) = momentFun Φ 1 := by
    funext A; rw [momentFun_eq]
  rw [heq]
  have hg : genPt d N (momentFun Φ 1) M = ((genMomentPt d N Φ 1 M : ℝ) : ℂ) := by
    rw [ofReal_genMomentPt h.contDiff 1 M]
    unfold genPt
    rw [one_div]
  rw [hg]
  have hval : ∀ q ∈ usedCoord d N,
      (gvar d (crd d N q) : ℝ) * (coordD2 d N (momentFun Φ 1) M q).re
        = (gvar d (crd d N q) : ℝ) * (2 * ‖coordD1 d N Φ M q‖ ^ 2)
          + (gvar d (crd d N q) : ℝ) * (2 * ((starRingEnd ℂ) (Φ M) * coordD2 d N Φ M q).re) := by
    intro q _
    rw [coordD2_momentFun_ofReal h.contDiff 1 M q, Complex.ofReal_re]
    norm_num
    ring
  have hM : genMomentPt d N Φ 1 M
      = quadVar d N Φ M + 2 * ((starRingEnd ℂ) (Φ M) * genD d N Φ M).re := by
    unfold genMomentPt
    rw [Finset.sum_congr rfl hval, Finset.sum_add_distrib]
    have hq1 : (∑ q ∈ usedCoord d N, (gvar d (crd d N q) : ℝ) * (2 * ‖coordD1 d N Φ M q‖ ^ 2))
        = 2 * quadVar d N Φ M := by
      unfold quadVar
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun q _ => by ring
    have hq2 : (∑ q ∈ usedCoord d N,
          (gvar d (crd d N q) : ℝ) * (2 * ((starRingEnd ℂ) (Φ M) * coordD2 d N Φ M q).re))
        = 2 * (2 * ((starRingEnd ℂ) (Φ M) * genD d N Φ M).re) := by
      rw [← sum_gvar_re_coordD2 (F := Φ) M, Finset.mul_sum]
      exact Finset.sum_congr rfl fun q _ => by ring
    rw [hq1, hq2]
    ring
  rw [hM]
  have hgd : genD d N Φ M = genPt d N Φ M := by
    unfold genD genPt
    rw [one_div]
  rw [hgd]
  congr 1
  ring

/-! ### T2: the one-step conditional variance -/

/-- The real expansion `‖a - b‖² = ‖a‖² - 2·Re(conj b · a) + ‖b‖²`, from `mul_conj_eq` and
`add_conj_mul` (`MomentGronwall.lean`). -/
private theorem norm_sub_sq_expand (a b : ℂ) :
    ‖a - b‖ ^ 2 = ‖a‖ ^ 2 - 2 * ((starRingEnd ℂ) b * a).re + ‖b‖ ^ 2 := by
  have e1 : ((‖a - b‖ ^ 2 : ℝ) : ℂ) = (a - b) * (starRingEnd ℂ) (a - b) :=
    (mul_conj_eq (a - b)).symm
  have e2 : (a - b) * (starRingEnd ℂ) (a - b)
      = a * (starRingEnd ℂ) a - (a * (starRingEnd ℂ) b + b * (starRingEnd ℂ) a)
        + b * (starRingEnd ℂ) b := by
    simp only [map_sub]; ring
  rw [e2, mul_conj_eq a, mul_conj_eq b, add_conj_mul a b] at e1
  have e3 : ((‖a - b‖ ^ 2 : ℝ) : ℂ)
      = ((‖a‖ ^ 2 - 2 * ((starRingEnd ℂ) b * a).re + ‖b‖ ^ 2 : ℝ) : ℂ) := by
    rw [e1]; push_cast; ring
  exact_mod_cast e3

/-- The real expansion `‖a + b‖² = ‖a‖² + 2·Re(conj b · a) + ‖b‖²`. -/
private theorem norm_add_sq_expand (a b : ℂ) :
    ‖a + b‖ ^ 2 = ‖a‖ ^ 2 + 2 * ((starRingEnd ℂ) b * a).re + ‖b‖ ^ 2 := by
  have e1 : ((‖a + b‖ ^ 2 : ℝ) : ℂ) = (a + b) * (starRingEnd ℂ) (a + b) :=
    (mul_conj_eq (a + b)).symm
  have e2 : (a + b) * (starRingEnd ℂ) (a + b)
      = a * (starRingEnd ℂ) a + (a * (starRingEnd ℂ) b + b * (starRingEnd ℂ) a)
        + b * (starRingEnd ℂ) b := by
    simp only [map_add]; ring
  rw [e2, mul_conj_eq a, mul_conj_eq b, add_conj_mul a b] at e1
  have e3 : ((‖a + b‖ ^ 2 : ℝ) : ℂ)
      = ((‖a‖ ^ 2 + 2 * ((starRingEnd ℂ) b * a).re + ‖b‖ ^ 2 : ℝ) : ℂ) := by
    rw [e1]; push_cast; ring
  exact_mod_cast e3

/-- **The variance identity** `E‖f - E f‖² = E‖f‖² - ‖E f‖²`, for an integrable `f : Ω d → ℂ`
whose `‖f‖²` is also integrable. Route: `‖f ω - μ‖² = ‖f ω‖² - 2·Re(conj μ · f ω) + ‖μ‖²`
(`norm_sub_sq_expand`), integrate termwise, and evaluate the cross term via
`MeasureTheory.integral_const_mul` and `mul_conj_eq`. -/
private theorem integral_normSq_sub_eq {d : Dims} {f : Ω d → ℂ} (hf : Integrable f (P d))
    (hf2 : Integrable (fun ω => ‖f ω‖ ^ 2) (P d)) :
    (∫ ω, ‖f ω - ∫ ω', f ω' ∂(P d)‖ ^ 2 ∂(P d))
      = (∫ ω, ‖f ω‖ ^ 2 ∂(P d)) - ‖∫ ω, f ω ∂(P d)‖ ^ 2 := by
  have hprob := isProbabilityMeasure_P d
  set μ : ℂ := ∫ ω, f ω ∂(P d) with hμ
  have hcrossInt : Integrable (fun ω => ((starRingEnd ℂ) μ * f ω).re) (P d) :=
    (hf.const_mul (starRingEnd ℂ μ)).re
  have hcross : (∫ ω, ((starRingEnd ℂ) μ * f ω).re ∂(P d)) = ‖μ‖ ^ 2 := by
    have h1 : (∫ ω, ((starRingEnd ℂ) μ * f ω).re ∂(P d))
        = (∫ ω, (starRingEnd ℂ) μ * f ω ∂(P d)).re := by
      have h := integral_re (hf.const_mul (starRingEnd ℂ μ))
      simpa [RCLike.re_eq_complex_re] using h
    rw [h1, integral_const_mul, ← hμ]
    have h2 : (starRingEnd ℂ) μ * μ = ((‖μ‖ ^ 2 : ℝ) : ℂ) := by
      rw [mul_comm]; exact mul_conj_eq μ
    rw [h2, Complex.ofReal_re]
  have hpt : ∀ ω, ‖f ω - μ‖ ^ 2 = ‖f ω‖ ^ 2 - 2 * ((starRingEnd ℂ) μ * f ω).re + ‖μ‖ ^ 2 :=
    fun ω => norm_sub_sq_expand (f ω) μ
  have step1 : (∫ ω, ‖f ω - μ‖ ^ 2 ∂(P d))
      = ∫ ω, (‖f ω‖ ^ 2 - 2 * ((starRingEnd ℂ) μ * f ω).re + ‖μ‖ ^ 2) ∂(P d) :=
    integral_congr_ae (Eventually.of_forall hpt)
  have step2 : (∫ ω, (‖f ω‖ ^ 2 - 2 * ((starRingEnd ℂ) μ * f ω).re + ‖μ‖ ^ 2) ∂(P d))
      = (∫ ω, ‖f ω‖ ^ 2 ∂(P d)) - 2 * (∫ ω, ((starRingEnd ℂ) μ * f ω).re ∂(P d)) + ‖μ‖ ^ 2 := by
    have hInt2 : Integrable (fun ω => ‖f ω‖ ^ 2 - 2 * ((starRingEnd ℂ) μ * f ω).re) (P d) :=
      hf2.sub (hcrossInt.const_mul 2)
    have hA : (∫ ω, (‖f ω‖ ^ 2 - 2 * ((starRingEnd ℂ) μ * f ω).re + ‖μ‖ ^ 2) ∂(P d))
        = (∫ ω, (‖f ω‖ ^ 2 - 2 * ((starRingEnd ℂ) μ * f ω).re) ∂(P d)) + ‖μ‖ ^ 2 := by
      rw [integral_add hInt2 (integrable_const _), MeasureTheory.integral_const]
      have huniv : (P d).real Set.univ = 1 := by simp
      rw [huniv, one_smul]
    have hBstep : (∫ ω, (‖f ω‖ ^ 2 - 2 * ((starRingEnd ℂ) μ * f ω).re) ∂(P d))
        = (∫ ω, ‖f ω‖ ^ 2 ∂(P d)) - 2 * (∫ ω, ((starRingEnd ℂ) μ * f ω).re ∂(P d)) := by
      rw [integral_sub hf2 (hcrossInt.const_mul 2), integral_const_mul]
    rw [hA, hBstep]
  rw [step1, step2, hcross]
  ring

/-- **T2.** `RBM.Gauss.Grid.oneStep_var_le`: the conditional variance of one grid increment is
`Δ ×` the quadratic-variation integrand of (5.25), up to `O(Δ^{3/2})`. -/
theorem oneStep_var_le (h : TestFun d N Φ) {M : Matrix (d.Idx N) (d.Idx N) ℂ}
    (hHerm : M.IsHermitian)
    {Λ₁ : ℝ}
    (hLip1 : ∀ A A' : Matrix (d.Idx N) (d.Idx N) ℂ, A.IsHermitian → A'.IsHermitian →
      ‖genPt d N Φ A - genPt d N Φ A'‖ ≤ Λ₁ * ‖A - A'‖)
    {Λ₂ : ℝ}
    (hLip2 : ∀ A A' : Matrix (d.Idx N) (d.Idx N) ℂ, A.IsHermitian → A'.IsHermitian →
      ‖genPt d N (fun A'' => ((‖Φ A''‖ ^ 2 : ℝ) : ℂ)) A
          - genPt d N (fun A'' => ((‖Φ A''‖ ^ 2 : ℝ) : ℂ)) A'‖ ≤ Λ₂ * ‖A - A'‖)
    {B : ℝ} (hB : ∀ A, ‖Φ A‖ ≤ B)
    {G : ℝ} (hG : ∀ A, ‖genPt d N Φ A‖ ≤ G)
    {Δ : ℝ} (hΔ : 0 ≤ Δ) :
    |(∫ ω, ‖Φ (M + (Real.sqrt Δ : ℂ) • Xmat d N ω)
          - ∫ ω', Φ (M + (Real.sqrt Δ : ℂ) • Xmat d N ω') ∂(P d)‖ ^ 2 ∂(P d))
        - Δ * quadVar d N Φ M|
      ≤ ((2 / 3) * Λ₂ * (∫ ω, ‖Xmat d N ω‖ ∂(P d))
          + (4 / 3) * B * Λ₁ * (∫ ω, ‖Xmat d N ω‖ ∂(P d))
          + 2 * G ^ 2
          + 2 * ((2 / 3) * Λ₁ * (∫ ω, ‖Xmat d N ω‖ ∂(P d))) ^ 2
          + 4 * B ^ 2)
        * (Δ ^ (3 / 2 : ℝ) + Δ ^ 2) := by
  classical
  have hprob := isProbabilityMeasure_P d
  set K : ℝ := ∫ ω, ‖Xmat d N ω‖ ∂(P d) with hK
  have hB0 : 0 ≤ B := le_trans (norm_nonneg (Φ M)) (hB M)
  have hG0 : 0 ≤ G := le_trans (norm_nonneg (genPt d N Φ M)) (hG M)
  have hK0 : 0 ≤ K := integral_nonneg fun ω => norm_nonneg _
  -- `Λ₁ K ≥ 0`, `Λ₂ K ≥ 0`: apply `oneStep_error_le` at the *fixed* auxiliary value `Δ' = 1`,
  -- independent of the theorem's own `Δ`, so no case split on `Δ` is needed for this.
  have hΨ : TestFun d N (fun A => ((‖Φ A‖ ^ 2 : ℝ) : ℂ)) := h.normSq
  have hΛ1K0 : 0 ≤ Λ₁ * K := by
    have haux := oneStep_error_le h hHerm hLip1 (show (0:ℝ) ≤ 1 by norm_num)
    rw [← hK, Real.one_rpow, mul_one] at haux
    nlinarith only [le_trans (norm_nonneg _) haux]
  have hΛ2K0 : 0 ≤ Λ₂ * K := by
    have haux := oneStep_error_le hΨ hHerm hLip2 (show (0:ℝ) ≤ 1 by norm_num)
    rw [← hK, Real.one_rpow, mul_one] at haux
    nlinarith only [le_trans (norm_nonneg _) haux]
  -- Continuity/boundedness of the shifted `Φ`.
  have hcontShift : Continuous fun ω : Ω d => Φ (M + (Real.sqrt Δ : ℂ) • Xmat d N ω) :=
    h.contDiff.continuous.comp (continuous_const.add
      ((continuous_const : Continuous fun _ : Ω d => (Real.sqrt Δ : ℂ)).smul
        (continuous_Xmat d N)))
  have hΦInt : Integrable (fun ω : Ω d => Φ (M + (Real.sqrt Δ : ℂ) • Xmat d N ω)) (P d) :=
    integrable_of_continuous_of_bound hcontShift fun ω => hB _
  have hΦ2Int :
      Integrable (fun ω : Ω d => ‖Φ (M + (Real.sqrt Δ : ℂ) • Xmat d N ω)‖ ^ 2) (P d) :=
    integrable_of_continuous_of_bound (hcontShift.norm.pow 2) fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hB _) 2
  set μ : ℂ := ∫ ω, Φ (M + (Real.sqrt Δ : ℂ) • Xmat d N ω) ∂(P d) with hμ
  -- Step A: `Var = E‖Φ‖² − ‖μ‖²`.
  have hVarEq :
      (∫ ω, ‖Φ (M + (Real.sqrt Δ : ℂ) • Xmat d N ω) - μ‖ ^ 2 ∂(P d))
        = (∫ ω, ‖Φ (M + (Real.sqrt Δ : ℂ) • Xmat d N ω)‖ ^ 2 ∂(P d)) - ‖μ‖ ^ 2 :=
    integral_normSq_sub_eq hΦInt hΦ2Int
  -- Step B: `oneStep_error_le` (T1486, T3) applied to `Φ` and to `‖Φ‖²`, at the theorem's `Δ`.
  have hE1 := oneStep_error_le h hHerm hLip1 hΔ
  rw [← hμ, ← hK] at hE1
  have hE2 := oneStep_error_le hΨ hHerm hLip2 hΔ
  rw [← hK] at hE2
  set ν : ℂ := ∫ ω, ((‖Φ (M + (Real.sqrt Δ : ℂ) • Xmat d N ω)‖ ^ 2 : ℝ) : ℂ) ∂(P d) with hν
  have hνeq : ν = ((∫ ω, ‖Φ (M + (Real.sqrt Δ : ℂ) • Xmat d N ω)‖ ^ 2 ∂(P d) : ℝ) : ℂ) := by
    rw [hν]; exact integral_ofReal
  set e1 : ℂ := μ - Φ M - (Δ : ℂ) • genPt d N Φ M with he1
  set e2 : ℂ :=
    ν - ((‖Φ M‖ ^ 2 : ℝ) : ℂ) - (Δ : ℂ) • genPt d N (fun A => ((‖Φ A‖ ^ 2 : ℝ) : ℂ)) M with he2
  have hE1' : ‖e1‖ ≤ (2 / 3) * Λ₁ * Δ ^ (3 / 2 : ℝ) * K := hE1
  have hE2' : ‖e2‖ ≤ (2 / 3) * Λ₂ * Δ ^ (3 / 2 : ℝ) * K := hE2
  have hr1_0 : 0 ≤ (2 / 3) * Λ₁ * Δ ^ (3 / 2 : ℝ) * K := le_trans (norm_nonneg e1) hE1'
  have hr2_0 : 0 ≤ (2 / 3) * Λ₂ * Δ ^ (3 / 2 : ℝ) * K := le_trans (norm_nonneg e2) hE2'
  -- Step C: `μ = Φ M + Δ · genPt Φ M + e1`, `ν = ‖Φ M‖² + Δ · genPt(‖Φ‖²) M + e2`.
  have hμval : μ = Φ M + (Δ : ℂ) • genPt d N Φ M + e1 := by rw [he1]; ring
  have hνval : ν = ((‖Φ M‖ ^ 2 : ℝ) : ℂ)
      + (Δ : ℂ) • genPt d N (fun A => ((‖Φ A‖ ^ 2 : ℝ) : ℂ)) M + e2 := by rw [he2]; ring
  have hquad : genPt d N (fun A => ((‖Φ A‖ ^ 2 : ℝ) : ℂ)) M
      = ((2 * ((starRingEnd ℂ) (Φ M) * genPt d N Φ M).re + quadVar d N Φ M : ℝ) : ℂ) :=
    genPt_normSq h M
  set S : ℂ := (Δ : ℂ) • genPt d N Φ M + e1 with hS
  have hSμ : S = μ - Φ M := by rw [hS, hμval]; ring
  -- Step D: the key real identity `E‖Φ‖² − ‖μ‖² = Δ·quadVar + e2.re − 2·Re(conj(ΦM)·e1) − ‖S‖²`.
  have hΔre : ∀ z : ℂ, ((Δ : ℂ) * z).re = Δ * z.re := by
    intro z; simp [Complex.mul_re]
  have hkey : (∫ ω, ‖Φ (M + (Real.sqrt Δ : ℂ) • Xmat d N ω)‖ ^ 2 ∂(P d)) - ‖μ‖ ^ 2
      = Δ * quadVar d N Φ M + e2.re - 2 * ((starRingEnd ℂ) (Φ M) * e1).re - ‖S‖ ^ 2 := by
    have hleft : (∫ ω, ‖Φ (M + (Real.sqrt Δ : ℂ) • Xmat d N ω)‖ ^ 2 ∂(P d)) = ν.re := by
      rw [hνeq, Complex.ofReal_re]
    have hνre : ν.re = ‖Φ M‖ ^ 2 + Δ * (2 * ((starRingEnd ℂ) (Φ M) * genPt d N Φ M).re
        + quadVar d N Φ M) + e2.re := by
      rw [hνval, hquad, Complex.add_re, Complex.add_re, Complex.sub_re, Complex.ofReal_re,
        smul_eq_mul, hΔre, Complex.ofReal_re]
    have hexp : ‖Φ M + S‖ ^ 2
        = ‖S‖ ^ 2 + 2 * ((starRingEnd ℂ) (Φ M) * S).re + ‖Φ M‖ ^ 2 := by
      have hcomm : S + Φ M = Φ M + S := add_comm _ _
      have := norm_add_sq_expand S (Φ M)
      rwa [hcomm] at this
    have hμnorm : ‖μ‖ ^ 2 = ‖Φ M‖ ^ 2 + 2 * ((starRingEnd ℂ) (Φ M) * S).re + ‖S‖ ^ 2 := by
      have heqμ : μ = Φ M + S := by rw [hSμ]; ring
      rw [heqμ, hexp]; ring
    have hScross : ((starRingEnd ℂ) (Φ M) * S).re
        = Δ * ((starRingEnd ℂ) (Φ M) * genPt d N Φ M).re + ((starRingEnd ℂ) (Φ M) * e1).re := by
      have : (starRingEnd ℂ) (Φ M) * S
          = (Δ : ℂ) * ((starRingEnd ℂ) (Φ M) * genPt d N Φ M) + (starRingEnd ℂ) (Φ M) * e1 := by
        rw [hS, smul_eq_mul]; ring
      rw [this, Complex.add_re, hΔre]
    rw [hleft, hνre, hμnorm, hScross]
    ring
  -- Step E: bound each error piece.
  have hΦMe1_bound :
      |((starRingEnd ℂ) (Φ M) * e1).re| ≤ B * ((2 / 3) * Λ₁ * Δ ^ (3 / 2 : ℝ) * K) := by
    calc |((starRingEnd ℂ) (Φ M) * e1).re| ≤ ‖(starRingEnd ℂ) (Φ M) * e1‖ :=
          Complex.abs_re_le_norm _
      _ = ‖Φ M‖ * ‖e1‖ := by rw [norm_mul, RCLike.norm_conj]
      _ ≤ B * ((2 / 3) * Λ₁ * Δ ^ (3 / 2 : ℝ) * K) := mul_le_mul (hB M) hE1' (norm_nonneg _) hB0
  have he2re_bound : |e2.re| ≤ (2 / 3) * Λ₂ * Δ ^ (3 / 2 : ℝ) * K :=
    le_trans (Complex.abs_re_le_norm e2) hE2'
  -- Step F: the two global bounds on `‖S‖`.
  have hS_bound1 : ‖S‖ ≤ Δ * G + (2 / 3) * Λ₁ * Δ ^ (3 / 2 : ℝ) * K := by
    have h1 : ‖S‖ ≤ ‖(Δ : ℂ) • genPt d N Φ M‖ + ‖e1‖ := by rw [hS]; exact norm_add_le _ _
    have h2 : ‖(Δ : ℂ) • genPt d N Φ M‖ = Δ * ‖genPt d N Φ M‖ := by
      rw [smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hΔ]
    calc ‖S‖ ≤ ‖(Δ : ℂ) • genPt d N Φ M‖ + ‖e1‖ := h1
      _ ≤ Δ * G + (2 / 3) * Λ₁ * Δ ^ (3 / 2 : ℝ) * K := by
          rw [h2]; exact add_le_add (mul_le_mul_of_nonneg_left (hG M) hΔ) hE1'
  have hμ_le_B : ‖μ‖ ≤ B := by
    calc ‖μ‖ ≤ ∫ ω, ‖Φ (M + (Real.sqrt Δ : ℂ) • Xmat d N ω)‖ ∂(P d) := by
          rw [hμ]; exact norm_integral_le_integral_norm _
      _ ≤ ∫ _ω : Ω d, B ∂(P d) := integral_mono hΦInt.norm (integrable_const B) fun ω => hB _
      _ = B := by
          rw [MeasureTheory.integral_const]
          have huniv : (P d).real Set.univ = 1 := by simp
          rw [huniv, one_smul]
  have hS_bound2 : ‖S‖ ≤ 2 * B := by
    rw [hSμ]
    calc ‖μ - Φ M‖ ≤ ‖μ‖ + ‖Φ M‖ := norm_sub_le _ _
      _ ≤ B + B := add_le_add hμ_le_B (hB M)
      _ = 2 * B := by ring
  -- From here on, only the *facts* about `K, μ, ν, e1, e2, S` established above are needed;
  -- forget their `let`-bodies so `linarith`/`nlinarith` do not try to unfold the whole chain
  -- `S → e1 → μ → …` (which otherwise times out `whnf`).
  clear_value S e2 e1 ν μ K
  -- Step G: `‖S‖² ≤ (2G² + 2((2/3)Λ₁K)² + 4B²)·(Δ^{3/2}+Δ²)`, by a case split at `Δ = 1`.
  have ht0 : 0 ≤ Δ ^ (3 / 2 : ℝ) := Real.rpow_nonneg hΔ _
  have ht20 : 0 ≤ Δ ^ 2 := sq_nonneg Δ
  have hsq32 : (Δ ^ (3 / 2 : ℝ)) ^ 2 = Δ ^ 3 := by
    rw [← Real.rpow_natCast (Δ ^ (3 / 2 : ℝ)) 2, ← Real.rpow_mul hΔ, ← Real.rpow_natCast Δ 3]
    congr 1
    norm_num
  have hΔ3le2 : Δ ≤ 1 → Δ ^ 3 ≤ Δ ^ 2 := by
    intro hcase
    have h1 : Δ ^ 2 * Δ ≤ Δ ^ 2 * 1 := mul_le_mul_of_nonneg_left hcase (sq_nonneg Δ)
    calc Δ ^ 3 = Δ ^ 2 * Δ := by ring
      _ ≤ Δ ^ 2 * 1 := h1
      _ = Δ ^ 2 := by ring
  have hΔ2ge1 : 1 ≤ Δ → 1 ≤ Δ ^ 2 := by
    intro hcase
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ Δ * Δ := mul_le_mul hcase hcase (by norm_num) hΔ
      _ = Δ ^ 2 := by ring
  have hS2_bound : ‖S‖ ^ 2
      ≤ (2 * G ^ 2 + 2 * ((2 / 3) * Λ₁ * K) ^ 2 + 4 * B ^ 2) * (Δ ^ (3 / 2 : ℝ) + Δ ^ 2) := by
    rcases le_total Δ 1 with hcase | hcase
    · -- `Δ ≤ 1`
      have hSsq_le : ‖S‖ ^ 2 ≤ (Δ * G + (2 / 3) * Λ₁ * Δ ^ (3 / 2 : ℝ) * K) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg S) hS_bound1 2
      have hexpand : (Δ * G + (2 / 3) * Λ₁ * Δ ^ (3 / 2 : ℝ) * K) ^ 2
          ≤ 2 * (Δ * G) ^ 2 + 2 * ((2 / 3) * Λ₁ * Δ ^ (3 / 2 : ℝ) * K) ^ 2 := by
        nlinarith only [sq_nonneg (Δ * G - (2 / 3) * Λ₁ * Δ ^ (3 / 2 : ℝ) * K)]
      have hrsq : ((2 / 3) * Λ₁ * Δ ^ (3 / 2 : ℝ) * K) ^ 2 = ((2 / 3) * Λ₁ * K) ^ 2 * Δ ^ 3 := by
        rw [← hsq32]; ring
      have h3le2 := hΔ3le2 hcase
      have hDG2 : (Δ * G) ^ 2 = G ^ 2 * Δ ^ 2 := by ring
      have hcombine : 2 * (Δ * G) ^ 2 + 2 * ((2 / 3) * Λ₁ * Δ ^ (3 / 2 : ℝ) * K) ^ 2
          ≤ (2 * G ^ 2 + 2 * ((2 / 3) * Λ₁ * K) ^ 2) * Δ ^ 2 := by
        rw [hrsq, hDG2]
        have h2 : ((2 / 3) * Λ₁ * K) ^ 2 * Δ ^ 3 ≤ ((2 / 3) * Λ₁ * K) ^ 2 * Δ ^ 2 :=
          mul_le_mul_of_nonneg_left h3le2 (sq_nonneg _)
        nlinarith only [h2]
      have hc0 : 0 ≤ 2 * G ^ 2 + 2 * ((2 / 3) * Λ₁ * K) ^ 2 := by positivity
      have hc0' : 0 ≤ 2 * G ^ 2 + 2 * ((2 / 3) * Λ₁ * K) ^ 2 + 4 * B ^ 2 := by positivity
      have hstepA : (2 * G ^ 2 + 2 * ((2 / 3) * Λ₁ * K) ^ 2) * Δ ^ 2
          ≤ (2 * G ^ 2 + 2 * ((2 / 3) * Λ₁ * K) ^ 2 + 4 * B ^ 2) * Δ ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith only [sq_nonneg B]) ht20
      have hstepB : (2 * G ^ 2 + 2 * ((2 / 3) * Λ₁ * K) ^ 2 + 4 * B ^ 2) * Δ ^ 2
          ≤ (2 * G ^ 2 + 2 * ((2 / 3) * Λ₁ * K) ^ 2 + 4 * B ^ 2) * (Δ ^ (3 / 2 : ℝ) + Δ ^ 2) :=
        mul_le_mul_of_nonneg_left (by linarith only [ht0]) hc0'
      linarith only [hSsq_le, hexpand, hcombine, hstepA, hstepB]
    · -- `1 ≤ Δ`
      have hSsq_le : ‖S‖ ^ 2 ≤ (2 * B) ^ 2 := pow_le_pow_left₀ (norm_nonneg S) hS_bound2 2
      have h4B2 : (2 * B) ^ 2 = 4 * B ^ 2 := by ring
      have h1 := hΔ2ge1 hcase
      have hc1 : 0 ≤ 2 * G ^ 2 + 2 * ((2 / 3) * Λ₁ * K) ^ 2 := by positivity
      have hc0 : 0 ≤ 2 * G ^ 2 + 2 * ((2 / 3) * Λ₁ * K) ^ 2 + 4 * B ^ 2 := by positivity
      have hstepA : (4 : ℝ) * B ^ 2 ≤ (2 * G ^ 2 + 2 * ((2 / 3) * Λ₁ * K) ^ 2 + 4 * B ^ 2) * 1 := by
        linarith only [hc1]
      have hstepB : (2 * G ^ 2 + 2 * ((2 / 3) * Λ₁ * K) ^ 2 + 4 * B ^ 2) * 1
          ≤ (2 * G ^ 2 + 2 * ((2 / 3) * Λ₁ * K) ^ 2 + 4 * B ^ 2) * Δ ^ 2 :=
        mul_le_mul_of_nonneg_left h1 hc0
      have hstepC : (2 * G ^ 2 + 2 * ((2 / 3) * Λ₁ * K) ^ 2 + 4 * B ^ 2) * Δ ^ 2
          ≤ (2 * G ^ 2 + 2 * ((2 / 3) * Λ₁ * K) ^ 2 + 4 * B ^ 2) * (Δ ^ (3 / 2 : ℝ) + Δ ^ 2) :=
        mul_le_mul_of_nonneg_left (by linarith only [ht0]) hc0
      linarith only [hSsq_le, h4B2, hstepA, hstepB, hstepC]
  -- Step H: assemble.
  rw [hVarEq]
  have hcancel : Δ * quadVar d N Φ M + e2.re - 2 * ((starRingEnd ℂ) (Φ M) * e1).re - ‖S‖ ^ 2
      - Δ * quadVar d N Φ M = e2.re - 2 * ((starRingEnd ℂ) (Φ M) * e1).re - ‖S‖ ^ 2 := by ring
  rw [hkey, hcancel]
  have habs : |e2.re - 2 * ((starRingEnd ℂ) (Φ M) * e1).re - ‖S‖ ^ 2|
      ≤ (2 / 3) * Λ₂ * Δ ^ (3 / 2 : ℝ) * K + 2 * (B * ((2 / 3) * Λ₁ * Δ ^ (3 / 2 : ℝ) * K))
        + ‖S‖ ^ 2 := by
    rw [abs_le]
    obtain ⟨ha1, ha2⟩ := abs_le.mp he2re_bound
    obtain ⟨hb1, hb2⟩ := abs_le.mp hΦMe1_bound
    constructor <;> linarith only [sq_nonneg ‖S‖, ha1, ha2, hb1, hb2]
  refine le_trans habs ?_
  have hcoefdiff : (0 : ℝ) ≤ (2 / 3) * Λ₂ * K + (4 / 3) * B * Λ₁ * K := by
    have h1 : (0 : ℝ) ≤ (2 / 3) * (Λ₂ * K) := mul_nonneg (by norm_num) hΛ2K0
    have h2 : (0 : ℝ) ≤ (4 / 3) * (B * (Λ₁ * K)) :=
      mul_nonneg (by norm_num) (mul_nonneg hB0 hΛ1K0)
    nlinarith only [h1, h2]
  have heq : (2 / 3) * Λ₂ * Δ ^ (3 / 2 : ℝ) * K + 2 * (B * ((2 / 3) * Λ₁ * Δ ^ (3 / 2 : ℝ) * K))
      = ((2 / 3) * Λ₂ * K + (4 / 3) * B * Λ₁ * K) * Δ ^ (3 / 2 : ℝ) := by ring
  have hnn2 : (0 : ℝ) ≤ ((2 / 3) * Λ₂ * K + (4 / 3) * B * Λ₁ * K) * Δ ^ 2 :=
    mul_nonneg hcoefdiff ht20
  have hexp : ((2 / 3) * Λ₂ * K + (4 / 3) * B * Λ₁ * K
        + 2 * G ^ 2 + 2 * ((2 / 3) * Λ₁ * K) ^ 2 + 4 * B ^ 2) * (Δ ^ (3 / 2 : ℝ) + Δ ^ 2)
      = ((2 / 3) * Λ₂ * K + (4 / 3) * B * Λ₁ * K) * Δ ^ (3 / 2 : ℝ)
        + (2 * G ^ 2 + 2 * ((2 / 3) * Λ₁ * K) ^ 2 + 4 * B ^ 2) * (Δ ^ (3 / 2 : ℝ) + Δ ^ 2)
        + ((2 / 3) * Λ₂ * K + (4 / 3) * B * Λ₁ * K) * Δ ^ 2 := by ring
  rw [heq, hexp]
  linarith only [hS2_bound, hnn2]

end Grid

end RBM.Gauss
