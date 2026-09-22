/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Step2Bootstrap
import RBM1D.Gauss.DischargeBDG
import RBM1D.Gauss.LoopC2

/-!
# The `TestFun` of route (A′), and the logarithmic derivative of the soft maximum (T250)

Route (A′) of Step 2's first bootstrap pass (paper §5.3, (5.39)–(5.47)) integrates by parts
against a **smooth** prefix weight instead of the prefix indicator, so Stein's identity
(`RBM.Gauss.MatrixStein.stein`, via `RBM.Gauss.hasDerivAt_integral_Phi`) applies on the full
measure and no bad-event remainder is produced.  That reduction is only legitimate once the
integrand is a `RBM.Gauss.TestFun`, i.e. `C²` with globally bounded value, differential and
second differential.  This file supplies the two pieces T230 could not take off the shelf.

## The chain rule for `RBM.Gauss.BddC2C`

`RBM1D/Gauss/LoopC2.lean` closes the quantitative `C²` class under sums, products and
post-composition with a **continuous linear** map, which is all a polynomial in the resolvent
needs.  Route (A′)'s integrand is not a polynomial: it is a cutoff profile *composed* with a
polynomial.  The missing closure property is therefore composition with a nonlinear real
function, and it is proved here:

* `RBM.Gauss.bddC2C_comp_real` — `‖D(g∘F)‖ ≤ c₁a₁` and `‖D²(g∘F)‖ ≤ c₂a₁² + c₁a₂`, with the
  bounds on `g`, `g'`, `g''` only required **at the points actually attained** by `F`.  That
  localisation is what lets `g = (·)^m` be used even though it is unbounded on `ℝ`.
* `RBM.Gauss.bddC2C_mul_real`, `RBM.Gauss.bddC2C_pow_real` — the real-scalar Leibniz rule and
  its iterate.

## The profile of route (A′)

The weight and the truncated moment are both built from `RBM.Cutoff.cutChi`, applied not to
the `ℓ^q` soft maximum `J̃` itself but to its `2r`-th power

`S := J̃^{2r} = ∑_{i} (‖f i‖ / T i)^{2r}`  (`RBM.Gauss.softSumObs`),

which is a *polynomial* in the entries of the resolvent and therefore has no `y ↦ y^{1/2r}`
singularity at the origin.  See the "Deviations" section at the end of the file: composing
through `J̃` itself is **not** `C²` unless `2r` divides `2p`.

* `RBM.Gauss.aprimeProfile Θ lvl r m y = χ(y/Θ^{2r}) · (cutTrunc lvl^{2r} y)^m` — the real
  profile, `C²` on all of `ℝ` (`RBM.Gauss.contDiff_aprimeProfile`).
* `RBM.Gauss.bddC2C_aprime`, `RBM.Gauss.testFun_aprime` — the resulting `TestFun`, with every
  constant explicit.
* `RBM.Gauss.aprimeProfile_eq_pow`, `RBM.Gauss.aprimeProfile_eq_zero_of_le` — the two facts the
  scheme uses: the profile is *exactly* `y^m` below the truncation level, and it *vanishes*
  once the soft maximum exceeds the cutoff level, so the weight really is a weight.

## The logarithmic derivative of the soft maximum, affine form

`RBM.Step2Bootstrap.abs_deriv_softMax_le` needs the purely logarithmic hypothesis
`|∂ρ_i| ≤ Λ|ρ_i|`, which cannot hold at a point where `ρ_i = 0` and `∂ρ_i ≠ 0` — and for
`ρ_i = |L - K|/T` that point is in the domain (it is `ω = 0`).  The honest hypothesis is the
**affine** one, `|∂ρ_i| ≤ Λ|ρ_i| + K`, and the point of the soft maximum survives it:

* `RBM.Step2Bootstrap.sum_pow_pred_le` — Hölder: `∑|ρ_i|^{2r-1} ≤ card^{1/2r}·(∑ρ_i^{2r})^{1-1/2r}`.
* `RBM.Step2Bootstrap.abs_deriv_softMax_le_affine` — `|∂J̃| ≤ Λ·J̃ + card^{1/2r}·K`.  The
  additive term carries `card^{1/2r} ≤ e` (by `RBM.Step2Bootstrap.rpow_card_le_exp_one`), **not**
  `card`: this is the whole gain of the soft maximum over the product weight of §4, and it is
  already there at `Λ = 0`, i.e. for a purely absolute entrywise derivative bound.
-/

namespace RBM

open Cutoff MomentDuhamelCut

open scoped Matrix.Norms.L2Operator

/-! ### 1. The chain rule for the quantitative `C²` class -/

namespace Gauss

section ChainRule

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The first differential of a real function composed with a real functional. -/
theorem fderiv_comp_real {F : E → ℝ} {g : ℝ → ℝ} (hF : Differentiable ℝ F)
    (hg : Differentiable ℝ g) (M : E) :
    fderiv ℝ (fun M => g (F M)) M = deriv g (F M) • fderiv ℝ F M := by
  have h := ((hg (F M)).hasDerivAt).comp_hasFDerivAt M ((hF M).hasFDerivAt)
  exact h.fderiv

/-- **⭐ `RBM.Gauss.BddC2C` is closed under post-composition with a `C²` real function.**

The bounds on `g`, `g'`, `g''` are only asked for **at the values actually taken by `F`**, which
is what makes the statement usable for profiles such as `y ↦ y^m` that are unbounded on `ℝ`. -/
theorem bddC2C_comp_real {F : E → ℝ} {g : ℝ → ℝ} {a₀ a₁ a₂ c₀ c₁ c₂ : ℝ}
    (hF : BddC2C F a₀ a₁ a₂) (hg : ContDiff ℝ 2 g)
    (hg₀ : ∀ M, |g (F M)| ≤ c₀) (hg₁ : ∀ M, |deriv g (F M)| ≤ c₁)
    (hg₂ : ∀ M, |deriv (deriv g) (F M)| ≤ c₂) :
    BddC2C (fun M => g (F M)) c₀ (c₁ * a₁) (c₂ * (a₁ * a₁) + c₁ * a₂) := by
  have hgd : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hgd' : Differentiable ℝ (deriv g) :=
    (hg.deriv' (n := 1)).differentiable one_ne_zero
  have hFd : Differentiable ℝ F := hF.differentiable
  have hcd : ContDiff ℝ 2 (fun M => g (F M)) := hg.comp hF.contDiff
  have hfd : ∀ M, fderiv ℝ (fun M => g (F M)) M = deriv g (F M) • fderiv ℝ F M :=
    fun M => fderiv_comp_real hFd hgd M
  have ha1 : 0 ≤ a₁ := hF.nonneg₁
  have hc1 : (0 : ℝ) ≤ c₁ := le_trans (abs_nonneg _) (hg₁ 0)
  have hc2 : (0 : ℝ) ≤ c₂ := le_trans (abs_nonneg _) (hg₂ 0)
  refine ⟨hcd, fun M => ?_, fun M => ?_, fun M => ?_⟩
  · simpa [Real.norm_eq_abs] using hg₀ M
  · rw [hfd M, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (hg₁ M) (hF.bdd₁ M) (norm_nonneg _) hc1
  -- the second differential: `g''·DF⊗DF + g'·D²F`
  · have hconst : (0 : ℝ) ≤ c₂ * (a₁ * a₁) + c₁ * a₂ := by
      have ha2 : 0 ≤ a₂ := hF.nonneg₂
      have : 0 ≤ c₂ * (a₁ * a₁) := mul_nonneg hc2 (mul_nonneg ha1 ha1)
      have : 0 ≤ c₁ * a₂ := mul_nonneg hc1 ha2
      positivity
    refine ContinuousLinearMap.opNorm_le_bound _ hconst fun B => ?_
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun A => ?_
    have key : fderiv ℝ (fderiv ℝ fun M => g (F M)) M B A
        = deriv (deriv g) (F M) * (fderiv ℝ F M B) * (fderiv ℝ F M A)
          + deriv g (F M) * (fderiv ℝ (fderiv ℝ F) M B A) := by
      have hlhs : HasDerivAt (fun t : ℝ => fderiv ℝ (fun M => g (F M)) (M + t • B) A)
          (fderiv ℝ (fderiv ℝ fun M => g (F M)) M B A) 0 := hasDerivAt_dir2' hcd M A B
      have hline : HasDerivAt (fun t : ℝ => F (M + t • B)) (fderiv ℝ F M B) 0 := by
        simpa using hasDerivAt_dir (hF.contDiff.of_le (by norm_num)) M B 0
      have h1 : HasDerivAt (fun t : ℝ => deriv g (F (M + t • B)))
          (deriv (deriv g) (F M) * (fderiv ℝ F M B)) 0 := by
        have hc := ((hgd' (F (M + (0 : ℝ) • B))).hasDerivAt).comp (0 : ℝ) hline
        simpa [Function.comp_def] using hc
      have h2 : HasDerivAt (fun t : ℝ => fderiv ℝ F (M + t • B) A)
          (fderiv ℝ (fderiv ℝ F) M B A) 0 := hasDerivAt_dir2' hF.contDiff M A B
      have hprod := h1.mul h2
      simp only [zero_smul, add_zero] at hprod
      have hrw : (fun t : ℝ => fderiv ℝ (fun M => g (F M)) (M + t • B) A)
          = fun t : ℝ => deriv g (F (M + t • B)) * (fderiv ℝ F (M + t • B) A) := by
        funext t
        rw [hfd (M + t • B)]
        simp
      rw [hrw] at hlhs
      have huniq := hlhs.unique hprod
      rw [huniq]
    rw [key]
    have dF1 : ∀ X : E, ‖fderiv ℝ F M X‖ ≤ a₁ * ‖X‖ := norm_fderiv_apply_le hF.bdd₁ M
    have dF2 : ‖fderiv ℝ (fderiv ℝ F) M B A‖ ≤ a₂ * ‖B‖ * ‖A‖ :=
      norm_fderiv2_apply_le hF.bdd₂ M B A
    have e1 : ‖deriv (deriv g) (F M) * (fderiv ℝ F M B) * (fderiv ℝ F M A)‖
        ≤ c₂ * (a₁ * ‖B‖) * (a₁ * ‖A‖) := by
      have hB : ‖fderiv ℝ F M B‖ ≤ a₁ * ‖B‖ := dF1 B
      have hA : ‖fderiv ℝ F M A‖ ≤ a₁ * ‖A‖ := dF1 A
      have hg : ‖deriv (deriv g) (F M)‖ ≤ c₂ := by
        simpa [Real.norm_eq_abs] using hg₂ M
      calc ‖deriv (deriv g) (F M) * (fderiv ℝ F M B) * (fderiv ℝ F M A)‖
          = ‖deriv (deriv g) (F M)‖ * ‖fderiv ℝ F M B‖ * ‖fderiv ℝ F M A‖ := by
            rw [norm_mul, norm_mul]
        _ ≤ c₂ * (a₁ * ‖B‖) * (a₁ * ‖A‖) := by
            gcongr
    have e2 : ‖deriv g (F M) * (fderiv ℝ (fderiv ℝ F) M B A)‖ ≤ c₁ * (a₂ * ‖B‖ * ‖A‖) := by
      have hg : ‖deriv g (F M)‖ ≤ c₁ := by simpa [Real.norm_eq_abs] using hg₁ M
      rw [norm_mul]
      exact mul_le_mul hg dF2 (norm_nonneg _) hc1
    calc ‖deriv (deriv g) (F M) * (fderiv ℝ F M B) * (fderiv ℝ F M A)
            + deriv g (F M) * (fderiv ℝ (fderiv ℝ F) M B A)‖
        ≤ ‖deriv (deriv g) (F M) * (fderiv ℝ F M B) * (fderiv ℝ F M A)‖
            + ‖deriv g (F M) * (fderiv ℝ (fderiv ℝ F) M B A)‖ := norm_add_le _ _
      _ ≤ c₂ * (a₁ * ‖B‖) * (a₁ * ‖A‖) + c₁ * (a₂ * ‖B‖ * ‖A‖) := add_le_add e1 e2
      _ = (c₂ * (a₁ * a₁) + c₁ * a₂) * ‖B‖ * ‖A‖ := by ring

end ChainRule
/-! ### 2. Real-scalar closure: products and powers -/

section RealScalar

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The Leibniz rule for two real-valued functionals. -/
theorem bddC2C_mul_real {F G : E → ℝ} {a₀ a₁ a₂ b₀ b₁ b₂ : ℝ}
    (hF : BddC2C F a₀ a₁ a₂) (hG : BddC2C G b₀ b₁ b₂) :
    BddC2C (fun M => F M * G M) (a₀ * b₀) (a₀ * b₁ + a₁ * b₀)
      (a₀ * b₂ + 2 * (a₁ * b₁) + a₂ * b₀) := by
  have hmul : ‖ContinuousLinearMap.mul ℝ ℝ‖ ≤ 1 := ContinuousLinearMap.opNorm_mul_le ℝ ℝ
  have hF' : BddC2C (fun M => ContinuousLinearMap.mul ℝ ℝ (F M)) a₀ a₁ a₂ :=
    (bddC2C_clm_comp (ContinuousLinearMap.mul ℝ ℝ) hF).mono
      (mul_le_of_le_one_left hF.nonneg₀ hmul) (mul_le_of_le_one_left hF.nonneg₁ hmul)
      (mul_le_of_le_one_left hF.nonneg₂ hmul)
  exact bddC2C_clm_apply hF' hG

/-- **Powers of a real functional**, through the chain rule: the constants are the honest
`a₀^m`, `m·a₀^{m-1}·a₁`, `m(m-1)a₀^{m-2}a₁² + m a₀^{m-1} a₂`. -/
theorem bddC2C_pow_real {F : E → ℝ} {a₀ a₁ a₂ : ℝ} (hF : BddC2C F a₀ a₁ a₂) (m : ℕ) :
    BddC2C (fun M => F M ^ m) (a₀ ^ m)
      ((m : ℝ) * a₀ ^ (m - 1) * a₁)
      (((m : ℝ) * ((m : ℝ) - 1) * a₀ ^ (m - 2)) * (a₁ * a₁)
        + ((m : ℝ) * a₀ ^ (m - 1)) * a₂) := by
  have ha0 : 0 ≤ a₀ := hF.nonneg₀
  have hb : ∀ M, |F M| ≤ a₀ := fun M => by simpa [Real.norm_eq_abs] using hF.bdd₀ M
  have hg : ContDiff ℝ 2 (fun y : ℝ => y ^ m) := contDiff_id.pow m
  have hd1 : deriv (fun y : ℝ => y ^ m) = fun y : ℝ => (m : ℝ) * y ^ (m - 1) := by
    funext y; simp
  have hd2 : ∀ y : ℝ, deriv (deriv fun y : ℝ => y ^ m) y
      = (m : ℝ) * ((m : ℝ) - 1) * y ^ (m - 2) := by
    intro y
    rw [hd1]
    rcases Nat.eq_zero_or_pos m with hm | hm
    · simp [hm]
    · have : deriv (fun y : ℝ => (m : ℝ) * y ^ (m - 1)) y
          = (m : ℝ) * (((m - 1 : ℕ) : ℝ) * y ^ (m - 1 - 1)) := by simp
      rw [this]
      have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
        have : (m - 1 : ℕ) + 1 = m := by omega
        have h2 : (((m - 1 : ℕ) : ℝ)) + 1 = (m : ℝ) := by
          exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) this
        linarith
      rw [hcast]
      have : m - 1 - 1 = m - 2 := by omega
      rw [this]; ring
  refine bddC2C_comp_real (g := fun y : ℝ => y ^ m) hF hg (fun M => ?_) (fun M => ?_)
    (fun M => ?_)
  · rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hb M) m
  · rw [hd1, abs_mul, abs_pow, Nat.abs_cast]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) (hb M) _) (by positivity)
  · rw [hd2, abs_mul, abs_mul, abs_pow, Nat.abs_cast]
    rcases Nat.eq_zero_or_pos m with hm | hm
    · simp [hm]
    · have hm1 : (0 : ℝ) ≤ (m : ℝ) - 1 := by
        have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
        linarith
      rw [abs_of_nonneg hm1]
      gcongr
      exact hb M

end RealScalar

/-! ### 3. The profile of the soft-max weight, and why it is `C²`

`RBM.Step2Bootstrap.softW r S ρ Θ = χ(J̃/Θ)` with `J̃ = (∑_i ρ_i^{2r})^{1/(2r)}`.  As a function
of the matrix `M` the inner sum is a *polynomial* in the entries of `Re G` and `Im G`, but the
`2r`-th root is not differentiable at the origin — and the origin is attained (it is the point
`L = K`).  The profile below is `χ` composed with the root, extended by `max y 0` below zero;
`RBM.Gauss.contDiff_softRootProfile` shows it is `C²` on all of `ℝ` nonetheless, because
`χ ≡ 1` on a neighbourhood of `0`, which is `RBM.Step2Bootstrap.cutChiD_softW_eq_zero` upgraded
from "the derivative vanishes" to "the function is locally constant".

The derivative bounds are obtained **not** by differentiating the root but from the fact that
the profile is constant off the compact window `[Θ^{2r}, (2Θ)^{2r}]`, so `g'` and `g''` are
continuous functions with compact support.  `RBM.Gauss.TestFun` asks for the constants
existentially, so nothing is lost. -/

section SoftRoot

open Step2Bootstrap

/-- The real profile of the soft-max weight: `χ` of the `2r`-th root. -/
noncomputable def softRootProfile (r : ℕ) (Θ : ℝ) (y : ℝ) : ℝ :=
  cutChi ((max y 0) ^ ((1 : ℝ) / (2 * (r : ℝ))) / Θ)

/-- On the nonnegative reals — the only values the soft-max sum takes — the profile *is*
`RBM.Step2Bootstrap.softW`. -/
theorem softRootProfile_eq_softW {ι : Type*} (r : ℕ) (Θ : ℝ) (S : Finset ι) (ρ : ι → ℝ) :
    softRootProfile r Θ (∑ i ∈ S, ρ i ^ (2 * r)) = softW r S ρ Θ := by
  rw [softRootProfile, softW, softMax,
    max_eq_left (sum_even_pow_nonneg S ρ r)]

theorem softRootProfile_le_one (r : ℕ) (Θ y : ℝ) : softRootProfile r Θ y ≤ 1 :=
  cutChi_le_one _
theorem softRootProfile_nonneg (r : ℕ) (Θ y : ℝ) : 0 ≤ softRootProfile r Θ y :=
  cutChi_nonneg _

theorem abs_softRootProfile_le_one (r : ℕ) (Θ y : ℝ) : |softRootProfile r Θ y| ≤ 1 :=
  abs_le.2 ⟨by linarith [softRootProfile_nonneg r Θ y], softRootProfile_le_one r Θ y⟩

variable {r : ℕ} {Θ : ℝ}

theorem rpow_pow_self (hΘ : 0 < Θ) (hr : 1 ≤ r) (c : ℝ) (hc : 0 ≤ c) :
    ((c * Θ) ^ (2 * r) : ℝ) ^ ((1 : ℝ) / (2 * (r : ℝ))) = c * Θ := by
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hcΘ : (0 : ℝ) ≤ c * Θ := by positivity
  rw [← Real.rpow_natCast (c * Θ) (2 * r), ← Real.rpow_mul hcΘ]
  push_cast
  rw [show (2 * (r : ℝ)) * ((1 : ℝ) / (2 * (r : ℝ))) = 1 by field_simp]
  exact Real.rpow_one _

/-- **The profile is `1` below the window** — this is where the `2r`-th root's singularity at
the origin hides. -/
theorem softRootProfile_eq_one_of_lt (hΘ : 0 < Θ) (hr : 1 ≤ r) {y : ℝ} (hy : y < Θ ^ (2 * r)) :
    softRootProfile r Θ y = 1 := by
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hα : (0 : ℝ) < (1 : ℝ) / (2 * (r : ℝ)) := by positivity
  refine cutChi_eq_one ?_
  rcases le_or_gt y 0 with hy0 | hy0
  · rw [max_eq_right hy0, Real.zero_rpow (ne_of_gt hα)]
    simp
  · rw [max_eq_left hy0.le, div_le_one hΘ]
    have h1 : y ^ ((1 : ℝ) / (2 * (r : ℝ))) < (Θ ^ (2 * r) : ℝ) ^ ((1 : ℝ) / (2 * (r : ℝ))) :=
      Real.rpow_lt_rpow hy0.le hy hα
    have h2 : (Θ ^ (2 * r) : ℝ) ^ ((1 : ℝ) / (2 * (r : ℝ))) = Θ := by
      simpa using rpow_pow_self hΘ hr 1 zero_le_one
    linarith [h2 ▸ h1]

/-- **The profile vanishes above the window**: the weight really cuts off. -/
theorem softRootProfile_eq_zero_of_gt (hΘ : 0 < Θ) (hr : 1 ≤ r) {y : ℝ}
    (hy : (2 * Θ) ^ (2 * r) ≤ y) : softRootProfile r Θ y = 0 := by
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hα : (0 : ℝ) < (1 : ℝ) / (2 * (r : ℝ)) := by positivity
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by positivity) hy
  refine cutChi_eq_zero ?_
  rw [max_eq_left hy0.le, le_div_iff₀ hΘ]
  have h1 : ((2 * Θ) ^ (2 * r) : ℝ) ^ ((1 : ℝ) / (2 * (r : ℝ)))
      ≤ y ^ ((1 : ℝ) / (2 * (r : ℝ))) :=
    Real.rpow_le_rpow (by positivity) hy hα.le
  have h2 : ((2 * Θ) ^ (2 * r) : ℝ) ^ ((1 : ℝ) / (2 * (r : ℝ))) = 2 * Θ :=
    rpow_pow_self hΘ hr 2 (by norm_num)
  linarith [h2 ▸ h1]

/-- **⭐ The profile is `C²` on all of `ℝ`.**  Away from the origin the `2r`-th root is smooth;
at and below the origin the profile is *constant*, so the singularity is never met.  This is
the `ContDiff` field of `RBM.Gauss.TestFun` for route (A′)'s weight — and it is exactly what
the product weight of §4, built from `J* = max_a`, cannot have. -/
theorem contDiff_softRootProfile (hΘ : 0 < Θ) (hr : 1 ≤ r) :
    ContDiff ℝ 2 (softRootProfile r Θ) := by
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hα : (0 : ℝ) < (1 : ℝ) / (2 * (r : ℝ)) := by positivity
  have hc : (0 : ℝ) < Θ ^ (2 * r) := by positivity
  rw [contDiff_iff_contDiffAt]
  intro x
  rcases lt_or_ge x (Θ ^ (2 * r)) with hx | hx
  · have hev : softRootProfile r Θ =ᶠ[nhds x] (fun _ : ℝ => (1 : ℝ)) := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      exact softRootProfile_eq_one_of_lt hΘ hr hy
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · have hx0 : 0 < x := lt_of_lt_of_le hc hx
    have hev : softRootProfile r Θ =ᶠ[nhds x]
        (fun y : ℝ => cutChi (y ^ ((1 : ℝ) / (2 * (r : ℝ))) / Θ)) := by
      filter_upwards [Ioi_mem_nhds hx0] with y hy
      rw [softRootProfile, max_eq_left hy.le]
    refine ContDiffAt.congr_of_eventuallyEq ?_ hev
    exact contDiff_cutChi.contDiffAt.comp x
      ((Real.contDiffAt_rpow_const_of_ne (ne_of_gt hx0)).div_const Θ)

/-- A continuous function that vanishes off a bounded window is globally bounded. -/
theorem exists_bound_of_vanishing_outside {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ}
    (hlo : ∀ y, y < a → f y = 0) (hhi : ∀ y, b < y → f y = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y, |f y| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    hf.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun y => ?_⟩
  rcases lt_or_ge y a with hy | hy
  · rw [hlo y hy]; simp
  · rcases lt_or_ge b y with hy' | hy'
    · rw [hhi y hy']; simp
    · exact le_trans (by simpa [Real.norm_eq_abs] using hC y ⟨hy, hy'⟩) (le_max_left _ _)

/-- The profile's first two derivatives vanish off the window `[Θ^{2r}, (2Θ)^{2r}]`, hence are
globally bounded. -/
theorem exists_deriv_bounds_softRootProfile (hΘ : 0 < Θ) (hr : 1 ≤ r) :
    ∃ c₁ c₂ : ℝ, 0 ≤ c₁ ∧ 0 ≤ c₂ ∧ (∀ y, |deriv (softRootProfile r Θ) y| ≤ c₁) ∧
      (∀ y, |deriv (deriv (softRootProfile r Θ)) y| ≤ c₂) := by
  have hcd := contDiff_softRootProfile hΘ hr
  have hd1 : ContDiff ℝ 1 (deriv (softRootProfile r Θ)) := hcd.deriv' (n := 1)
  have hd2 : Continuous (deriv (deriv (softRootProfile r Θ))) :=
    (hd1.deriv' (n := 0)).continuous
  have hlo1 : ∀ y, y < Θ ^ (2 * r) → deriv (softRootProfile r Θ) y = 0 := by
    intro y hy
    have hev : softRootProfile r Θ =ᶠ[nhds y] (fun _ : ℝ => (1 : ℝ)) := by
      filter_upwards [Iio_mem_nhds hy] with z hz
      exact softRootProfile_eq_one_of_lt hΘ hr hz
    rw [hev.deriv_eq]; simp
  have hhi1 : ∀ y, (2 * Θ) ^ (2 * r) < y → deriv (softRootProfile r Θ) y = 0 := by
    intro y hy
    have hev : softRootProfile r Θ =ᶠ[nhds y] (fun _ : ℝ => (0 : ℝ)) := by
      filter_upwards [Ioi_mem_nhds hy] with z hz
      exact softRootProfile_eq_zero_of_gt hΘ hr hz.le
    rw [hev.deriv_eq]; simp
  have hlo2 : ∀ y, y < Θ ^ (2 * r) → deriv (deriv (softRootProfile r Θ)) y = 0 := by
    intro y hy
    have hev : deriv (softRootProfile r Θ) =ᶠ[nhds y] (fun _ : ℝ => (0 : ℝ)) := by
      filter_upwards [Iio_mem_nhds hy] with z hz
      exact hlo1 z hz
    rw [hev.deriv_eq]; simp
  have hhi2 : ∀ y, (2 * Θ) ^ (2 * r) < y → deriv (deriv (softRootProfile r Θ)) y = 0 := by
    intro y hy
    have hev : deriv (softRootProfile r Θ) =ᶠ[nhds y] (fun _ : ℝ => (0 : ℝ)) := by
      filter_upwards [Ioi_mem_nhds hy] with z hz
      exact hhi1 z hz
    rw [hev.deriv_eq]; simp
  obtain ⟨c₁, hc₁0, hc₁⟩ :=
    exists_bound_of_vanishing_outside (hd1.continuous) hlo1 hhi1
  obtain ⟨c₂, hc₂0, hc₂⟩ := exists_bound_of_vanishing_outside hd2 hlo2 hhi2
  exact ⟨c₁, c₂, hc₁0, hc₂0, hc₁, hc₂⟩

end SoftRoot

/-! ### 4. The `TestFun` of route (A′)

`RBM.Gauss.hasDerivAt_integral_Phi` consumes `TestFun d N Φ` for

`Φ M = (softW r S (fun i => ρ i M) Θ : ℂ) · Ψ M`,

with `Ψ` the (bounded, `C²`) moment factor `(Uker … )^{2p}` that `RBM1D/Gauss/LoopC2.lean`
already produces as a `RBM.Gauss.BddC2C`.  The theorem below is that assembly. -/

section TestFunAssembly

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Step2Bootstrap

theorem norm_ofRealCLM_le : ‖Complex.ofRealCLM‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by simp

/-- Embedding a real functional in `ℂ` keeps all three constants. -/
theorem bddC2C_ofReal {F : E → ℝ} {a₀ a₁ a₂ : ℝ} (hF : BddC2C F a₀ a₁ a₂) :
    BddC2C (fun M => ((F M : ℝ) : ℂ)) a₀ a₁ a₂ := by
  have h := bddC2C_clm_comp Complex.ofRealCLM hF
  exact h.mono (mul_le_of_le_one_left hF.nonneg₀ norm_ofRealCLM_le)
    (mul_le_of_le_one_left hF.nonneg₁ norm_ofRealCLM_le)
    (mul_le_of_le_one_left hF.nonneg₂ norm_ofRealCLM_le)

/-- The Leibniz rule for two `ℂ`-valued functionals. -/
theorem bddC2C_mul_complex {F G : E → ℂ} {a₀ a₁ a₂ b₀ b₁ b₂ : ℝ}
    (hF : BddC2C F a₀ a₁ a₂) (hG : BddC2C G b₀ b₁ b₂) :
    BddC2C (fun M => F M * G M) (a₀ * b₀) (a₀ * b₁ + a₁ * b₀)
      (a₀ * b₂ + 2 * (a₁ * b₁) + a₂ * b₀) := by
  have hmul : ‖ContinuousLinearMap.mul ℝ ℂ‖ ≤ 1 := ContinuousLinearMap.opNorm_mul_le ℝ ℂ
  have hF' : BddC2C (fun M => ContinuousLinearMap.mul ℝ ℂ (F M)) a₀ a₁ a₂ :=
    (bddC2C_clm_comp (ContinuousLinearMap.mul ℝ ℂ) hF).mono
      (mul_le_of_le_one_left hF.nonneg₀ hmul) (mul_le_of_le_one_left hF.nonneg₁ hmul)
      (mul_le_of_le_one_left hF.nonneg₂ hmul)
  exact bddC2C_clm_apply hF' hG

/-- **⭐ The soft-max weight is a quantitative `C²` functional.**  `bdd₀` is `softW_le_one`;
the derivative constants are the (existential) bounds of
`RBM.Gauss.exists_deriv_bounds_softRootProfile` times the constants of the polynomial
`∑_i ρ_i^{2r}`. -/
theorem exists_bddC2C_softW {ι : Type*} {S : Finset ι} {ρ : ι → E → ℝ} {r : ℕ} {Θ : ℝ}
    {a₀ a₁ a₂ : ℝ} (hr : 1 ≤ r) (hΘ : 0 < Θ)
    (hsum : BddC2C (fun M => ∑ i ∈ S, ρ i M ^ (2 * r)) a₀ a₁ a₂) :
    ∃ c₁ c₂ : ℝ, BddC2C (fun M => softW r S (fun i => ρ i M) Θ) 1 c₁ c₂ := by
  obtain ⟨c₁, c₂, _, _, hc₁, hc₂⟩ := exists_deriv_bounds_softRootProfile (r := r) hΘ hr
  refine ⟨c₁ * a₁, c₂ * (a₁ * a₁) + c₁ * a₂, ?_⟩
  have hfun : (fun M => softW r S (fun i => ρ i M) Θ)
      = fun M => softRootProfile r Θ (∑ i ∈ S, ρ i M ^ (2 * r)) := by
    funext M; rw [softRootProfile_eq_softW]
  rw [hfun]
  exact bddC2C_comp_real hsum (contDiff_softRootProfile hΘ hr)
    (fun M => abs_softRootProfile_le_one r Θ _) (fun M => hc₁ _) (fun M => hc₂ _)

variable {d : Dims} {N : ℕ}

/-- **⭐⭐ The `TestFun` instance of route (A′).**  `Φ = (soft-max weight) · (moment factor)`
is `C²` with globally bounded value, differential and second differential, so
`RBM.Gauss.hasDerivAt_integral_Phi` applies to it on the **full** measure — which is the whole
point of replacing the prefix indicator by a smooth weight.

The hypotheses are exactly two `RBM.Gauss.BddC2C`s: one for the *polynomial* `∑_i ρ_i^{2r}`
(supplied by `RBM.Gauss.bddC2C_pow_real` and `RBM.Gauss.bddC2C_sum` from a `BddC2C` for each
ratio `ρ_i`), one for the moment factor `Ψ` (supplied by `RBM1D/Gauss/LoopC2.lean`). -/
theorem testFun_softW_mul {ι : Type*} {S : Finset ι}
    {ρ : ι → Matrix (d.Idx N) (d.Idx N) ℂ → ℝ} {Ψ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}
    {r : ℕ} {Θ : ℝ} {a₀ a₁ a₂ b₀ b₁ b₂ : ℝ} (hr : 1 ≤ r) (hΘ : 0 < Θ)
    (hsum : BddC2C (fun M => ∑ i ∈ S, ρ i M ^ (2 * r)) a₀ a₁ a₂)
    (hΨ : BddC2C Ψ b₀ b₁ b₂) :
    TestFun d N (fun M => ((softW r S (fun i => ρ i M) Θ : ℝ) : ℂ) * Ψ M) := by
  obtain ⟨c₁, c₂, hW⟩ := exists_bddC2C_softW hr hΘ hsum
  exact TestFun.of_bddC2' ((bddC2C_mul_complex (bddC2C_ofReal hW) hΨ).bddC2)

end TestFunAssembly

end Gauss

/-! ### 5. The logarithmic derivative bound, affine form

`RBM.Step2Bootstrap.LogDerivBound S ρ ρ' Λ`, i.e. `|ρ'_i| ≤ Λ|ρ_i|` with **no** additive term,
is *refuted* at any point where some `ρ_i` vanishes and `ρ'_i` does not
(`RBM.Step2Bootstrap.not_logDerivBound_of_zero`), and for `ρ_i = ‖L-K‖/T` that point is in the
domain (it is `L = K`, the deterministic configuration).  The repair is the affine hypothesis,
and the gain of the soft maximum survives it: the additive term is multiplied by
`(card)^{1/2r} ≤ e`, **not** by `card`. -/

namespace Step2Bootstrap

variable {ι : Type*}

/-- **Hölder**: `∑_i |ρ_i|^{2r-1} ≤ card^{1/2r} · (∑_i ρ_i^{2r})^{1-1/2r}`.  This is the one
step that keeps the additive term of the affine bound free of a cardinality factor. -/
theorem sum_abs_pow_pred_le {S : Finset ι} {ρ : ι → ℝ} {r : ℕ} (hr : 1 ≤ r) :
    ∑ i ∈ S, |ρ i| ^ (2 * r - 1)
      ≤ (S.card : ℝ) ^ ((1 : ℝ) / (2 * (r : ℝ))) *
        (∑ i ∈ S, ρ i ^ (2 * r)) ^ (1 - (1 : ℝ) / (2 * (r : ℝ))) := by
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < (r : ℝ) := by linarith
  set n : ℝ := 2 * (r : ℝ) with hn
  have hn0 : (0 : ℝ) < n := by simp only [hn]; linarith
  have hn1 : (1 : ℝ) ≤ n - 1 := by simp only [hn]; linarith
  have hnm : ((2 * r - 1 : ℕ) : ℝ) = n - 1 := by
    have h1 : (2 * r - 1 : ℕ) + 1 = 2 * r := by omega
    have h2 : (((2 * r - 1 : ℕ) : ℝ)) + 1 = 2 * (r : ℝ) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) h1
    simp only [hn]; linarith
  set p : ℝ := n / (n - 1) with hp
  have hp1 : 1 ≤ p := by rw [hp, le_div_iff₀ (by linarith)]; linarith
  have hpinv : p⁻¹ = 1 - 1 / n := by rw [hp, inv_div]; field_simp
  have key := Real.inner_le_weight_mul_Lp_of_nonneg S hp1 (fun _ => (1 : ℝ))
    (fun i => |ρ i| ^ (2 * r - 1)) (fun _ => zero_le_one) (fun i => by positivity)
  simp only [one_mul] at key
  have hcard : ∑ _i ∈ S, (1 : ℝ) = (S.card : ℝ) := by simp
  have hterm : ∀ i ∈ S, (|ρ i| ^ (2 * r - 1) : ℝ) ^ p = ρ i ^ (2 * r) := by
    intro i _
    rw [← Real.rpow_natCast (|ρ i|) (2 * r - 1), ← Real.rpow_mul (abs_nonneg _), hnm]
    have hq : (n - 1) * p = n := by rw [hp]; field_simp
    rw [hq, hn, show (2 * (r : ℝ)) = ((2 * r : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    exact abs_even_pow _ _
  rw [hcard, Finset.sum_congr rfl hterm, hpinv] at key
  simpa using key

/-- **⭐⭐ The affine (honest) form of the cardinality-loss-free derivative estimate.**

`abs_deriv_softMax_le` asks for `|ρ'_i| ≤ Λ|ρ_i|`; the model only gives
`|ρ'_i| ≤ Λ|ρ_i| + K` (and in fact `Λ = 0`, `K` = the absolute derivative bound, is already
enough).  The conclusion keeps the shape: the additive term costs `(card)^{1/2r}`, which
`rpow_card_le_exp_one` calibrates to `e`.  **The gain over the product weight of §4 is entirely
here** — `abs_derivProd_le` would produce `card · K`. -/
theorem abs_deriv_softMax_le_affine {r : ℕ} (hr : 1 ≤ r) {S : Finset ι}
    {ρ ρ' : ι → ℝ} {Λ K : ℝ} (hK : 0 ≤ K)
    (h : ∀ i ∈ S, |ρ' i| ≤ Λ * |ρ i| + K) (hY : 0 < ∑ i ∈ S, ρ i ^ (2 * r)) :
    |(∑ i ∈ S, ((2 * r : ℕ) : ℝ) * ρ i ^ (2 * r - 1) * ρ' i) * ((1 : ℝ) / (2 * (r : ℝ))) *
        (∑ i ∈ S, ρ i ^ (2 * r)) ^ ((1 : ℝ) / (2 * (r : ℝ)) - 1)|
      ≤ Λ * softMax r S ρ + (S.card : ℝ) ^ ((1 : ℝ) / (2 * (r : ℝ))) * K := by
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hn0 : (0 : ℝ) < 2 * (r : ℝ) := by linarith
  set n : ℝ := 2 * (r : ℝ) with hn
  set Y : ℝ := ∑ i ∈ S, ρ i ^ (2 * r) with hYdef
  set T : ℝ := ∑ i ∈ S, |ρ i| ^ (2 * r - 1) with hTdef
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun i _ => by positivity
  have hYb0 : 0 ≤ Y ^ ((1 : ℝ) / n - 1) := Real.rpow_nonneg hY.le _
  have hcast : |((2 * r : ℕ) : ℝ)| = n := by rw [Nat.cast_mul]; simp [abs_of_nonneg, hn]
  have hnum : |∑ i ∈ S, ((2 * r : ℕ) : ℝ) * ρ i ^ (2 * r - 1) * ρ' i|
      ≤ n * (Λ * Y + K * T) := by
    have hbd : ∀ i ∈ S, |((2 * r : ℕ) : ℝ) * ρ i ^ (2 * r - 1) * ρ' i|
        ≤ n * (Λ * ρ i ^ (2 * r) + K * |ρ i| ^ (2 * r - 1)) := by
      intro i hi
      rw [abs_mul, abs_mul, hcast, abs_pow]
      have hstep : |ρ i| ^ (2 * r - 1) * |ρ' i| ≤ |ρ i| ^ (2 * r - 1) * (Λ * |ρ i| + K) :=
        mul_le_mul_of_nonneg_left (h i hi) (by positivity)
      have hid : |ρ i| ^ (2 * r - 1) * (Λ * |ρ i| + K)
          = Λ * ρ i ^ (2 * r) + K * |ρ i| ^ (2 * r - 1) := by
        have hcnt : 2 * r - 1 + 1 = 2 * r := by omega
        have h1 : |ρ i| ^ (2 * r - 1) * |ρ i| = ρ i ^ (2 * r) := by
          calc |ρ i| ^ (2 * r - 1) * |ρ i| = |ρ i| ^ (2 * r - 1) * |ρ i| ^ 1 := by ring
            _ = |ρ i| ^ (2 * r) := by rw [← pow_add, hcnt]
            _ = ρ i ^ (2 * r) := abs_even_pow _ _
        calc |ρ i| ^ (2 * r - 1) * (Λ * |ρ i| + K)
            = Λ * (|ρ i| ^ (2 * r - 1) * |ρ i|) + K * |ρ i| ^ (2 * r - 1) := by ring
          _ = Λ * ρ i ^ (2 * r) + K * |ρ i| ^ (2 * r - 1) := by rw [h1]
      calc n * |ρ i| ^ (2 * r - 1) * |ρ' i|
          = n * (|ρ i| ^ (2 * r - 1) * |ρ' i|) := by ring
        _ ≤ n * (|ρ i| ^ (2 * r - 1) * (Λ * |ρ i| + K)) :=
            mul_le_mul_of_nonneg_left hstep hn0.le
        _ = n * (Λ * ρ i ^ (2 * r) + K * |ρ i| ^ (2 * r - 1)) := by rw [hid]
    calc |∑ i ∈ S, ((2 * r : ℕ) : ℝ) * ρ i ^ (2 * r - 1) * ρ' i|
        ≤ ∑ i ∈ S, |((2 * r : ℕ) : ℝ) * ρ i ^ (2 * r - 1) * ρ' i| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ S, n * (Λ * ρ i ^ (2 * r) + K * |ρ i| ^ (2 * r - 1)) := Finset.sum_le_sum hbd
      _ = n * (Λ * Y + K * T) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hYpow : Y ^ ((1 : ℝ) / n - 1) * Y = softMax r S ρ := by
    have h1 : Y ^ ((1 : ℝ) / n - 1) * Y ^ (1 : ℝ) = Y ^ ((1 : ℝ) / n - 1 + 1) :=
      (Real.rpow_add hY _ _).symm
    rw [Real.rpow_one] at h1
    rw [softMax, ← hYdef, h1, sub_add_cancel]
  have hTY : T * Y ^ ((1 : ℝ) / n - 1) ≤ (S.card : ℝ) ^ ((1 : ℝ) / n) := by
    have hH : T ≤ (S.card : ℝ) ^ ((1 : ℝ) / n) * Y ^ (1 - (1 : ℝ) / n) := sum_abs_pow_pred_le hr
    have hmul := mul_le_mul_of_nonneg_right hH hYb0
    refine hmul.trans (le_of_eq ?_)
    have hone : Y ^ (1 - (1 : ℝ) / n) * Y ^ ((1 : ℝ) / n - 1) = 1 := by
      rw [← Real.rpow_add hY]; simp
    calc (S.card : ℝ) ^ ((1 : ℝ) / n) * Y ^ (1 - (1 : ℝ) / n) * Y ^ ((1 : ℝ) / n - 1)
        = (S.card : ℝ) ^ ((1 : ℝ) / n) * (Y ^ (1 - (1 : ℝ) / n) * Y ^ ((1 : ℝ) / n - 1)) := by
          ring
      _ = (S.card : ℝ) ^ ((1 : ℝ) / n) := by rw [hone, mul_one]
  rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 : ℝ) / n),
    abs_of_nonneg hYb0]
  calc |∑ i ∈ S, ((2 * r : ℕ) : ℝ) * ρ i ^ (2 * r - 1) * ρ' i| * ((1 : ℝ) / n) *
        Y ^ ((1 : ℝ) / n - 1)
      ≤ n * (Λ * Y + K * T) * ((1 : ℝ) / n) * Y ^ ((1 : ℝ) / n - 1) := by gcongr
    _ = Λ * (Y ^ ((1 : ℝ) / n - 1) * Y) + K * (T * Y ^ ((1 : ℝ) / n - 1)) := by field_simp
    _ ≤ Λ * softMax r S ρ + K * ((S.card : ℝ) ^ ((1 : ℝ) / n)) := by rw [hYpow]; gcongr
    _ = Λ * softMax r S ρ + (S.card : ℝ) ^ ((1 : ℝ) / n) * K := by ring

/-- **⭐ The purely logarithmic bound is unsatisfiable at a zero of the entry.**  If some
`ρ_i` vanishes while `ρ'_i` does not, **no** `Λ` satisfies `LogDerivBound`.  Recorded as a
satisfiability guard: the producer of the entrywise bound must deliver the *affine* shape. -/
theorem not_logDerivBound_of_zero {S : Finset ι} {ρ ρ' : ι → ℝ} {i : ι} (hi : i ∈ S)
    (hρ : ρ i = 0) (hρ' : ρ' i ≠ 0) (Λ : ℝ) : ¬ LogDerivBound S ρ ρ' Λ := by
  intro h
  have := h i hi
  rw [hρ] at this
  simp only [abs_zero, mul_zero] at this
  exact hρ' (abs_eq_zero.1 (le_antisymm this (abs_nonneg _)))

/-- The affine bound *is* satisfiable there: at `Λ = 0` it is the absolute derivative bound. -/
theorem logDerivBoundAffine_of_abs {S : Finset ι} {ρ ρ' : ι → ℝ} {K : ℝ}
    (h : ∀ i ∈ S, |ρ' i| ≤ K) : ∀ i ∈ S, |ρ' i| ≤ (0 : ℝ) * |ρ i| + K := by
  intro i hi; simpa using h i hi

end Step2Bootstrap

/-! ### 6. The matrix-level form, and why the multiplicative-only shape is refuted -/

namespace Gauss

variable {d : Dims} {N : ℕ}

/-- **The shape `‖∂_α F‖ ≤ Λ‖F‖` is false at a zero of `F`.**  Concretely: at a Hermitian `M`
where the loop error `L - K` vanishes but its coordinate derivative does not, no polynomial
`Λ(d, N, u)` can make `abs_coordD1_lkFun_le` (the §12 target of
`RBM1D/Gauss/Step2Bootstrap.lean`) true.  The additive term is therefore not optional. -/
theorem not_coordD1_le_mul_norm {F : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}
    {M : Matrix (d.Idx N) (d.Idx N) ℂ} {q : d.Idx N × d.Idx N × Bool}
    (h0 : F M = 0) (h1 : coordD1 d N F M q ≠ 0) (Λ : ℝ) :
    ¬ ‖coordD1 d N F M q‖ ≤ Λ * ‖F M‖ := by
  intro h
  rw [h0, norm_zero, mul_zero] at h
  exact h1 (norm_eq_zero.1 (le_antisymm h (norm_nonneg _)))

/-- **The affine bound the model does supply**, with `Λ = 0`: the coordinate derivative of a
quantitative `C²` observable is bounded by `a₁‖B_α‖`, uniformly in `M`.  Fed into
`RBM.Step2Bootstrap.abs_deriv_softMax_le_affine` this gives `|∂J̃| ≤ card^{1/2r}·K`, i.e. the
cardinality-loss-free estimate route (A′) needs. -/
theorem abs_coordD1_le_affine {F : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} {a₀ a₁ a₂ : ℝ}
    (hF : BddC2C F a₀ a₁ a₂) (M : Matrix (d.Idx N) (d.Idx N) ℂ)
    (q : d.Idx N × d.Idx N × Bool) :
    ‖coordD1 d N F M q‖
      ≤ (0 : ℝ) * ‖F M‖ + a₁ * ‖Bmat d N q.1 q.2.1 q.2.2‖ := by
  rw [zero_mul, zero_add, coordD1]
  exact norm_fderiv_apply_le hF.bdd₁ M _

end Gauss

/-! ### 7. Non-degeneracy

`TestFun` is satisfied by every constant, so the instance above has to be shown non-trivial.
The profile of the weight takes **both** values `0` and `1`, so `Φ` is not a constant and the
cutoff really cuts off. -/

namespace Gauss

section NonDegenerate

open Step2Bootstrap

theorem softRootProfile_zero {r : ℕ} {Θ : ℝ} (hΘ : 0 < Θ) (hr : 1 ≤ r) :
    softRootProfile r Θ 0 = 1 :=
  softRootProfile_eq_one_of_lt hΘ hr (by positivity)

theorem softRootProfile_top {r : ℕ} {Θ : ℝ} (hΘ : 0 < Θ) (hr : 1 ≤ r) :
    softRootProfile r Θ ((2 * Θ) ^ (2 * r)) = 0 :=
  softRootProfile_eq_zero_of_gt hΘ hr le_rfl

/-- **The weight is not constant**, so `RBM.Gauss.testFun_softW_mul` is not satisfied
vacuously by a constant `Φ`. -/
theorem softRootProfile_ne_const {r : ℕ} {Θ : ℝ} (hΘ : 0 < Θ) (hr : 1 ≤ r) :
    softRootProfile r Θ 0 ≠ softRootProfile r Θ ((2 * Θ) ^ (2 * r)) := by
  rw [softRootProfile_zero hΘ hr, softRootProfile_top hΘ hr]
  norm_num

/-- A compiled witness that the hypotheses of `RBM.Gauss.testFun_softW_mul` are simultaneously
satisfiable by a **non-constant** observable: the trace of the regularised resolvent at
`z = i`, with `S` a singleton and `Ψ ≡ 1`. -/
theorem sat_testFun_softW_mul (d : Dims) (N : ℕ) {r : ℕ} (hr : 1 ≤ r) {Θ : ℝ} (hΘ : 0 < Θ) :
    TestFun d N (fun M => ((softW r ({0} : Finset (Fin 1))
        (fun _ => (Matrix.trace (resH (n := d.Idx N) Complex.I M)).re) Θ : ℝ) : ℂ) *
      (1 : ℂ)) := by
  have hz : (Complex.I : ℂ).im ≠ 0 := by simp
  have hzη : (1 : ℝ) ≤ |(Complex.I : ℂ).im| := by simp
  have hres := bddC2C_resH (n := d.Idx N) hz one_pos hzη
  have htr := bddC2C_clm_comp (traceCLM (d.Idx N)) hres
  have hre := bddC2C_clm_comp Complex.reCLM htr
  have hpow := bddC2C_pow_real hre (2 * r)
  have hsum := bddC2C_sum ({0} : Finset (Fin 1))
    (f := fun _ (M : Matrix (d.Idx N) (d.Idx N) ℂ) =>
      (Complex.reCLM (traceCLM (d.Idx N) (resH (n := d.Idx N) Complex.I M))) ^ (2 * r))
    (fun _ _ => hpow)
  exact testFun_softW_mul hr hΘ hsum (bddC2C_const (1 : ℂ))

end NonDegenerate

end Gauss

end RBM

/-!
## Deviations from the paper

**T250a** (§5.3, (5.39)–(5.47); Stein/generator in §5.2).

1. *The paper's prefix indicator is replaced by the smooth soft-max weight.*  This is route
   (A′), already recorded by T230; the present file only supplies its analytic side.  No
   change to the paper is proposed; the deviation is a strengthening of the Lean statement
   (full-measure integration by parts instead of a conditional one).
2. *The entrywise derivative bound is affine, not purely multiplicative.*  §12 of
   `RBM1D/Gauss/Step2Bootstrap.lean` states the target as
   `‖∂_α (L-K)‖ ≤ Λ · ‖L-K‖` with no additive term.  That statement is **false** at any point
   where `L = K` and `∂_α L ≠ 0` (`RBM.Gauss.not_coordD1_le_mul_norm`), and `L = K` is in the
   domain.  The Lean statement therefore carries an additive deterministic term,
   `‖∂_α(L-K)‖ ≤ Λ‖L-K‖ + K₀`, and the soft-max estimate is generalised accordingly
   (`RBM.Step2Bootstrap.abs_deriv_softMax_le_affine`).  The paper's estimate is unaffected:
   the additive term costs `(card)^{1/2r} ≤ e`, not `card`, so the "no cardinality loss"
   property that motivates the soft maximum is preserved.  Affected lines: the display after
   (5.44).  No renumbering.
3. *The `2r`-th root is read through `max y 0`.*  `softW` is composed with the polynomial
   `∑_i ρ_i^{2r} ≥ 0`, so the two agree pointwise
   (`RBM.Gauss.softRootProfile_eq_softW`); the truncation only fixes a `C²` extension of the
   profile below `0`, where it is constant anyway.  Not a mathematical deviation.
-/
