/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Flow.EnergyUniform

/-!
# Theorem 2.4 ((2.6)–(2.9)) at an `N`-dependent energy

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, "Proof of Theorems 2.3 and 2.4" in
§2.6.

The statements of Theorem 2.4 at an `N`-dependent Lemma 2.8 energy `E : ℕ → ℝ`, on the
`N`-dependent hypotheses `RBM.SpecSeqN`, `RBM.BoundsCoreN` and `RBM.BoundsN` of
`Flow/EnergyUniform.lean`:

* (2.6)/(2.7) in loop form and in `≺` form: `RBM.loop2_of_boundsCoreN`,
  `RBM.quantumDiffusion_pm_of_boundsCoreN`, `RBM.quantumDiffusion_pp_of_boundsCoreN`; in
  probability form: `RBM.quantumDiffusion_pm_prob_of_boundsCoreN`,
  `RBM.quantumDiffusion_pp_prob_of_boundsCoreN`.
* (2.8)/(2.9), the expectations, in loop form and in deterministic `≺` form:
  `RBM.expect_loop2_of_boundsN`, `RBM.expect_quantumDiffusion_pm_of_boundsN`,
  `RBM.expect_quantumDiffusion_pp_of_boundsN`; with the explicit factor `W ^ τ'`:
  `RBM.expect_quantumDiffusion_pm_W_of_boundsN`, `RBM.expect_quantumDiffusion_pp_W_of_boundsN`.
  These use the expectation bound (2.71), the field `RBM.BoundsN.expect`.
-/

namespace RBM

open MeasureTheory Filter

section Main

open scoped Matrix

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {X : Sample B} {κ τ : ℝ} {E : ℕ → ℝ}
  {z : ℕ → ℂ}

/-- **Theorem 2.4, (2.6)/(2.7)** in loop form at an `N`-dependent energy, from (2.60) for `n = 2`
and (2.66), on `RBM.BoundsCoreN`. -/
theorem loop2_of_boundsCoreN (T : Transfer X) (hκ : 0 < κ) (hz : SpecSeqN κ τ E z)
    (hB : BoundsCoreN X E (fun N => lemT (z N))) (σ₂ : Bool) :
    StochDom B.P (fun N (ab : ZMod (B.L N) × ZMod (B.L N)) ω =>
        ‖gloop (B.L N) (B.W N) (T.Hband N ω) (z N) ⟨[true, σ₂], [ab.1, ab.2]⟩ -
          (lemT (z N) : ℂ) * B.Kval (E N) N (lemT (z N)) ⟨[true, σ₂], [ab.1, ab.2]⟩‖)
      (fun N _ _ => (B.zScale N (z N))⁻¹ ^ 2) := by
  have h1 := ((hB.LmK 2 (by norm_num)).trans
    (StochDom.of_unifDetDom (hz.unifDetDom_pow hκ 2))).precomp_param
    (fun N (ab : ZMod (B.L N) × ZMod (B.L N)) =>
      ((![true, σ₂], ![ab.1, ab.2]) : LoopData (B.L N) 2))
  refine T.loop2 z hz.im_pos σ₂
    (fun N ab => (lemT (z N) : ℂ) * B.Kval (E N) N (lemT (z N)) ⟨[true, σ₂], [ab.1, ab.2]⟩) _
    (StochDom.of_le_left (fun N ab ω => ?_) h1)
  rw [LoopData.idx_two, hz.lemE_eq N, Sample.lkErr, ← mul_sub, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (hz.lemT_nonneg N)]
  exact mul_le_of_le_one_left (norm_nonneg _) (hz.lemT_lt_one' N).le

/-- **Theorem 2.4, (2.6)** at an `N`-dependent energy, on `RBM.BoundsCoreN`. -/
theorem quantumDiffusion_pm_of_boundsCoreN (T : Transfer X) (hκ : 0 < κ) (hz : SpecSeqN κ τ E z)
    (hB : BoundsCoreN X E (fun N => lemT (z N))) :
    StochDom B.P (fun N (ab : ZMod (B.L N) × ZMod (B.L N)) ω =>
        ‖(green (T.Hband N ω) (z N) * Eblk (B.L N) (B.W N) ab.1 *
            (green (T.Hband N ω) (z N))ᴴ * Eblk (B.L N) (B.W N) ab.2).trace -
          (B.W N : ℂ)⁻¹ * ((‖msc (z N)‖ ^ 2 : ℝ) : ℂ) *
            Theta (B.L N) ((‖msc (z N)‖ ^ 2 : ℝ) : ℂ) ab.1 ab.2‖)
      (fun N _ _ => (B.zScale N (z N))⁻¹ ^ 2) := by
  refine StochDom.of_le_left (fun N ab ω => le_of_eq ?_) (loop2_of_boundsCoreN T hκ hz hB false)
  rw [gloop_pm_eq (T.hermitian N ω), ← hz.lemE_eq N, B.lemT_mul_Kval_pm N (hz.im_pos N)]

/-- **Theorem 2.4, (2.7)** at an `N`-dependent energy, on `RBM.BoundsCoreN`. -/
theorem quantumDiffusion_pp_of_boundsCoreN (T : Transfer X) (hκ : 0 < κ) (hz : SpecSeqN κ τ E z)
    (hB : BoundsCoreN X E (fun N => lemT (z N))) :
    StochDom B.P (fun N (ab : ZMod (B.L N) × ZMod (B.L N)) ω =>
        ‖(green (T.Hband N ω) (z N) * Eblk (B.L N) (B.W N) ab.1 *
            green (T.Hband N ω) (z N) * Eblk (B.L N) (B.W N) ab.2).trace -
          (B.W N : ℂ)⁻¹ * msc (z N) ^ 2 * Theta (B.L N) (msc (z N) ^ 2) ab.1 ab.2‖)
      (fun N _ _ => (B.zScale N (z N))⁻¹ ^ 2) := by
  refine StochDom.of_le_left (fun N ab ω => le_of_eq ?_) (loop2_of_boundsCoreN T hκ hz hB true)
  rw [gloop_pp_eq, ← hz.lemE_eq N, B.lemT_mul_Kval_pp N (hz.im_pos N)]

/-- **Theorem 2.4, (2.8)/(2.9)** in loop form at an `N`-dependent energy, from (2.62) and (2.66)
in expectation, on `RBM.BoundsN`. -/
theorem expect_loop2_of_boundsN (T : Transfer X) (hκ : 0 < κ) (hz : SpecSeqN κ τ E z)
    (hB : BoundsN X E (fun N => lemT (z N))) (σ₂ : Bool) :
    UnifDetDom (fun N (ab : ZMod (B.L N) × ZMod (B.L N)) =>
        ‖(∫ ω, gloop (B.L N) (B.W N) (T.Hband N ω) (z N) ⟨[true, σ₂], [ab.1, ab.2]⟩ ∂B.P) -
          (lemT (z N) : ℂ) * B.Kval (E N) N (lemT (z N)) ⟨[true, σ₂], [ab.1, ab.2]⟩‖)
      (fun N _ => (B.zScale N (z N))⁻¹ ^ 3) := by
  have h1 := (hB.expect.precomp_param
    (fun N (ab : ZMod (B.L N) × ZMod (B.L N)) =>
      ((![true, σ₂], ![ab.1, ab.2]) : LoopData (B.L N) 2))).trans (hz.unifDetDom_pow hκ 3)
  refine UnifDetDom.mono_left (Eventually.of_forall fun N ab => ?_) h1
  rw [T.loop2_expect z hz.im_pos σ₂ N ab.1 ab.2, LoopData.idx_two, hz.lemE_eq N, Sample.expErr,
    ← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hz.lemT_nonneg N)]
  exact mul_le_of_le_one_left (norm_nonneg _) (hz.lemT_lt_one' N).le

/-- **Theorem 2.4, (2.8)** at an `N`-dependent energy, on `RBM.BoundsN` (deterministic `≺`). -/
theorem expect_quantumDiffusion_pm_of_boundsN (T : Transfer X) (hκ : 0 < κ)
    (hz : SpecSeqN κ τ E z) (hB : BoundsN X E (fun N => lemT (z N))) :
    UnifDetDom (fun N (ab : ZMod (B.L N) × ZMod (B.L N)) =>
        ‖(∫ ω, (green (T.Hband N ω) (z N) * Eblk (B.L N) (B.W N) ab.1 *
            (green (T.Hband N ω) (z N))ᴴ * Eblk (B.L N) (B.W N) ab.2).trace ∂B.P) -
          (B.W N : ℂ)⁻¹ * ((‖msc (z N)‖ ^ 2 : ℝ) : ℂ) *
            Theta (B.L N) ((‖msc (z N)‖ ^ 2 : ℝ) : ℂ) ab.1 ab.2‖)
      (fun N _ => (B.zScale N (z N))⁻¹ ^ 3) := by
  refine UnifDetDom.mono_left (Eventually.of_forall fun N ab => le_of_eq ?_)
    (expect_loop2_of_boundsN T hκ hz hB false)
  have hfun : (fun ω => (green (T.Hband N ω) (z N) * Eblk (B.L N) (B.W N) ab.1 *
      (green (T.Hband N ω) (z N))ᴴ * Eblk (B.L N) (B.W N) ab.2).trace) =
      fun ω => gloop (B.L N) (B.W N) (T.Hband N ω) (z N) ⟨[true, false], [ab.1, ab.2]⟩ :=
    funext fun ω => (gloop_pm_eq (T.hermitian N ω) _ _ _).symm
  rw [hfun, ← hz.lemE_eq N, B.lemT_mul_Kval_pm N (hz.im_pos N)]

/-- **Theorem 2.4, (2.9)** at an `N`-dependent energy, on `RBM.BoundsN` (deterministic `≺`). -/
theorem expect_quantumDiffusion_pp_of_boundsN (T : Transfer X) (hκ : 0 < κ)
    (hz : SpecSeqN κ τ E z) (hB : BoundsN X E (fun N => lemT (z N))) :
    UnifDetDom (fun N (ab : ZMod (B.L N) × ZMod (B.L N)) =>
        ‖(∫ ω, (green (T.Hband N ω) (z N) * Eblk (B.L N) (B.W N) ab.1 *
            green (T.Hband N ω) (z N) * Eblk (B.L N) (B.W N) ab.2).trace ∂B.P) -
          (B.W N : ℂ)⁻¹ * msc (z N) ^ 2 * Theta (B.L N) (msc (z N) ^ 2) ab.1 ab.2‖)
      (fun N _ => (B.zScale N (z N))⁻¹ ^ 3) := by
  refine UnifDetDom.mono_left (Eventually.of_forall fun N ab => le_of_eq ?_)
    (expect_loop2_of_boundsN T hκ hz hB true)
  have hfun : (fun ω => (green (T.Hband N ω) (z N) * Eblk (B.L N) (B.W N) ab.1 *
      green (T.Hband N ω) (z N) * Eblk (B.L N) (B.W N) ab.2).trace) =
      fun ω => gloop (B.L N) (B.W N) (T.Hband N ω) (z N) ⟨[true, true], [ab.1, ab.2]⟩ :=
    funext fun ω => (gloop_pp_eq _ _ _ _).symm
  rw [hfun, ← hz.lemE_eq N, B.lemT_mul_Kval_pp N (hz.im_pos N)]

/-- **Theorem 2.4, (2.6), paper form** at an `N`-dependent energy, on `RBM.BoundsCoreN`. -/
theorem quantumDiffusion_pm_prob_of_boundsCoreN (T : Transfer X) (hκ : 0 < κ)
    (hz : SpecSeqN κ τ E z) (hB : BoundsCoreN X E (fun N => lemT (z N))) {τ' D : ℝ}
    (hτ' : 0 < τ') (hD : 0 < D) :
    ∀ᶠ N : ℕ in atTop, B.P {ω | ∃ ab : ZMod (B.L N) × ZMod (B.L N),
      (B.W N : ℝ) ^ τ' * (B.zScale N (z N))⁻¹ ^ 2 <
        ‖(green (T.Hband N ω) (z N) * Eblk (B.L N) (B.W N) ab.1 *
            (green (T.Hband N ω) (z N))ᴴ * Eblk (B.L N) (B.W N) ab.2).trace -
          (B.W N : ℂ)⁻¹ * ((‖msc (z N)‖ ^ 2 : ℝ) : ℂ) *
            Theta (B.L N) ((‖msc (z N)‖ ^ 2 : ℝ) : ℂ) ab.1 ab.2‖}
      ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) :=
  B.prob_le_of_stochDom (fun N _ _ => pow_nonneg (hz.zScale_inv_nonneg N) _)
    (quantumDiffusion_pm_of_boundsCoreN T hκ hz hB) hτ' hD

/-- **Theorem 2.4, (2.7), paper form** at an `N`-dependent energy, on `RBM.BoundsCoreN`. -/
theorem quantumDiffusion_pp_prob_of_boundsCoreN (T : Transfer X) (hκ : 0 < κ)
    (hz : SpecSeqN κ τ E z) (hB : BoundsCoreN X E (fun N => lemT (z N))) {τ' D : ℝ}
    (hτ' : 0 < τ') (hD : 0 < D) :
    ∀ᶠ N : ℕ in atTop, B.P {ω | ∃ ab : ZMod (B.L N) × ZMod (B.L N),
      (B.W N : ℝ) ^ τ' * (B.zScale N (z N))⁻¹ ^ 2 <
        ‖(green (T.Hband N ω) (z N) * Eblk (B.L N) (B.W N) ab.1 *
            green (T.Hband N ω) (z N) * Eblk (B.L N) (B.W N) ab.2).trace -
          (B.W N : ℂ)⁻¹ * msc (z N) ^ 2 * Theta (B.L N) (msc (z N) ^ 2) ab.1 ab.2‖}
      ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) :=
  B.prob_le_of_stochDom (fun N _ _ => pow_nonneg (hz.zScale_inv_nonneg N) _)
    (quantumDiffusion_pp_of_boundsCoreN T hκ hz hB) hτ' hD

/-- **Theorem 2.4, (2.8), paper form** at an `N`-dependent energy, on `RBM.BoundsN`. -/
theorem expect_quantumDiffusion_pm_W_of_boundsN (T : Transfer X) (hκ : 0 < κ)
    (hz : SpecSeqN κ τ E z) (hB : BoundsN X E (fun N => lemT (z N))) {τ' : ℝ} (hτ' : 0 < τ') :
    ∀ᶠ N : ℕ in atTop, ∀ ab : ZMod (B.L N) × ZMod (B.L N),
      ‖(∫ ω, (green (T.Hband N ω) (z N) * Eblk (B.L N) (B.W N) ab.1 *
            (green (T.Hband N ω) (z N))ᴴ * Eblk (B.L N) (B.W N) ab.2).trace ∂B.P) -
          (B.W N : ℂ)⁻¹ * ((‖msc (z N)‖ ^ 2 : ℝ) : ℂ) *
            Theta (B.L N) ((‖msc (z N)‖ ^ 2 : ℝ) : ℂ) ab.1 ab.2‖ ≤
        (B.W N : ℝ) ^ τ' * (B.zScale N (z N))⁻¹ ^ 3 :=
  B.le_W_rpow_of_unifDetDom (fun N _ => pow_nonneg (hz.zScale_inv_nonneg N) _)
    (expect_quantumDiffusion_pm_of_boundsN T hκ hz hB) hτ'

/-- **Theorem 2.4, (2.9), paper form** at an `N`-dependent energy, on `RBM.BoundsN`. -/
theorem expect_quantumDiffusion_pp_W_of_boundsN (T : Transfer X) (hκ : 0 < κ)
    (hz : SpecSeqN κ τ E z) (hB : BoundsN X E (fun N => lemT (z N))) {τ' : ℝ} (hτ' : 0 < τ') :
    ∀ᶠ N : ℕ in atTop, ∀ ab : ZMod (B.L N) × ZMod (B.L N),
      ‖(∫ ω, (green (T.Hband N ω) (z N) * Eblk (B.L N) (B.W N) ab.1 *
            green (T.Hband N ω) (z N) * Eblk (B.L N) (B.W N) ab.2).trace ∂B.P) -
          (B.W N : ℂ)⁻¹ * msc (z N) ^ 2 * Theta (B.L N) (msc (z N) ^ 2) ab.1 ab.2‖ ≤
        (B.W N : ℝ) ^ τ' * (B.zScale N (z N))⁻¹ ^ 3 :=
  B.le_W_rpow_of_unifDetDom (fun N _ => pow_nonneg (hz.zScale_inv_nonneg N) _)
    (expect_quantumDiffusion_pp_of_boundsN T hκ hz hB) hτ'

end Main

section Compat

open scoped Matrix

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {X : Sample B} {κ τ E : ℝ} {z : ℕ → ℂ}

end Compat

end RBM
