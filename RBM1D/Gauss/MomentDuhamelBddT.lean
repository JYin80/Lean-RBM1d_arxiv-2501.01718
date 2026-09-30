/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import RBM1D.Hierarchy.DriftDef
import RBM1D.Gauss.MomentDuhamelGauss
import RBM1D.Gauss.TestFunHerm

/-!
# Joint regularity in `(time, matrix)` for the moment route's `Ψ`

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.2.  The moment route differentiates

  `Ψ(u, M) = |(U_{u,v} ∘ (L - K)_u)_a|^{2p}`

in the running time `u`, which enters `Ψ` in three places at once: the spectral parameter
`z_u = E + (1-u) m_E`, the propagator's running time, and `K_u`.  This file supplies the
regularity of the first two.

## Main results

* `RBM.Gauss.contDiffAt_Gsig_zt_pair`, `RBM.Gauss.contDiffAt_gloopProd_zt_pair`,
  `RBM.Gauss.contDiffAt_loopObs_zt_pair` — `(u, M) ↦ L_{σ,a}(z_u, M)` is jointly `C²`, at every
  matrix: the pair-variable form of `RBM.EGDef.contDiffAt_gloopProd_matrix`, by induction over
  the `n` factors of (2.41) on top of `RBM.Gauss.contDiffAt_resH_path`.
* `RBM.Gauss.continuous_edgeKer_time` — `u ↦ (U_{u,v})_{xy}` is continuous.
* `RBM.Gauss.le_abs_im_zt_of_le`, `RBM.Gauss.im_zt_ne_zero_of_le` — on a window ending strictly
  before `1` the spectral parameter stays off the real axis, with an explicit `η`.
-/

namespace RBM

open MeasureTheory Filter Real Set

namespace Gauss

open scoped Matrix.Norms.L2Operator NNReal InnerProductSpace

variable {d : Dims} {N : ℕ}

/-! ### The propagator's running time moves as well -/

/-- `u ↦ (U_{u,v})_{xy}` is continuous — it is affine in `u`, `RBM.hasDerivAt_edgeKer`. -/
theorem continuous_edgeKer_time {L : ℕ} [NeZero L] (ξ t : ℂ) (x y : ZMod L) :
    Continuous fun r : ℝ => edgeKer L ξ (r : ℂ) t x y :=
  continuous_iff_continuousAt.2 fun r => (hasDerivAt_edgeKer L ξ t x y r).continuousAt

/-! ### Joint regularity in `(time, matrix)`

`RBM.Gauss.contDiffAt_resH_path` has the resolvent jointly `C²` along a `C²` path of spectral
parameters; the induction over the `n` factors of (2.41) **in the pair variable** gives the pair
version of `RBM.EGDef.contDiffAt_gloopProd_matrix`.  Since `RBM.Gauss.loopObs` carries
`RBM.Gauss.hermCLM`, the statement holds at *every* matrix, with no Hermitian side condition. -/

/-- `(u, M) ↦ G(σ)(hermCLM M, z_u)` is jointly `C²`. -/
theorem contDiffAt_Gsig_zt_pair (Ev : ℝ) {u : ℝ} (hz : (zt Ev u).im ≠ 0) (σ : Bool)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    ContDiffAt ℝ 2 (fun q : ℝ × Matrix (d.Idx N) (d.Idx N) ℂ =>
      Gsig (hermCLM (d.Idx N) q.2) (zt Ev q.1) σ) (u, M) := by
  have hfun : (fun q : ℝ × Matrix (d.Idx N) (d.Idx N) ℂ =>
      Gsig (hermCLM (d.Idx N) q.2) (zt Ev q.1) σ)
      = fun q : ℝ × Matrix (d.Idx N) (d.Idx N) ℂ =>
        resH ((Ev : ℂ) + (1 - (q.1 : ℂ)) * mSigma Ev σ) q.2 := by
    funext q
    rw [Gsig_zt, resH_eq_green]
  rw [hfun]
  refine contDiffAt_resH_path (z := fun s : ℝ => (Ev : ℂ) + (1 - (s : ℂ)) * mSigma Ev σ)
    ?_ (ztSig_im_ne_zero hz σ) M
  exact (contDiff_const.add
    ((contDiff_const.sub Complex.ofRealCLM.contDiff).mul contDiff_const)).contDiffAt

/-- **The pair version of `RBM.EGDef.contDiffAt_gloopProd_matrix`.** -/
theorem contDiffAt_gloopProd_zt_pair (Ev : ℝ) {u : ℝ} (hz : (zt Ev u).im ≠ 0)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    ∀ (σ : List Bool) (a : List (ZMod (d.L N))),
      ContDiffAt ℝ 2 (fun q : ℝ × Matrix (d.Idx N) (d.Idx N) ℂ =>
        gloopProd (d.L N) (d.W N) (hermCLM (d.Idx N) q.2) (zt Ev q.1) ⟨σ, a⟩) (u, M) := by
  intro σ
  induction σ with
  | nil => intro a; exact contDiffAt_const
  | cons σ₀ σ ih =>
      intro a
      cases a with
      | nil => exact contDiffAt_const
      | cons c a' =>
          have hfun : (fun q : ℝ × Matrix (d.Idx N) (d.Idx N) ℂ =>
              gloopProd (d.L N) (d.W N) (hermCLM (d.Idx N) q.2) (zt Ev q.1)
                (⟨σ₀ :: σ, c :: a'⟩ : LoopIdx (ZMod (d.L N))))
              = fun q : ℝ × Matrix (d.Idx N) (d.Idx N) ℂ =>
                Gsig (hermCLM (d.Idx N) q.2) (zt Ev q.1) σ₀ * Eblk (d.L N) (d.W N) c
                  * gloopProd (d.L N) (d.W N) (hermCLM (d.Idx N) q.2) (zt Ev q.1)
                      ⟨σ, a'⟩ := rfl
          rw [hfun]
          exact ((contDiffAt_Gsig_zt_pair Ev hz σ₀ M).mul contDiffAt_const).mul (ih a')

/-- **`(u, M) ↦ L_{σ,a}(z_u, M)` is jointly `C²`**, at every matrix. -/
theorem contDiffAt_loopObs_zt_pair (Ev : ℝ) {u : ℝ} (hz : (zt Ev u).im ≠ 0)
    (I : LoopIdx (ZMod (d.L N))) (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    ContDiffAt ℝ 2 (fun q : ℝ × Matrix (d.Idx N) (d.Idx N) ℂ =>
      loopObs d N (zt Ev q.1) I q.2) (u, M) := by
  set T : Matrix (d.Idx N) (d.Idx N) ℂ →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap
      ((Matrix.traceLinearMap (d.Idx N) ℂ ℂ).restrictScalars ℝ) with hTdef
  have hfun : (fun q : ℝ × Matrix (d.Idx N) (d.Idx N) ℂ => loopObs d N (zt Ev q.1) I q.2)
      = T ∘ fun q : ℝ × Matrix (d.Idx N) (d.Idx N) ℂ =>
          gloopProd (d.L N) (d.W N) (hermCLM (d.Idx N) q.2) (zt Ev q.1) I := rfl
  rw [hfun]
  exact (T.contDiff (n := 2)).contDiffAt.comp (u, M)
    (contDiffAt_gloopProd_zt_pair Ev hz M I.σ I.a)

/-! ### The spectral parameter stays off the real axis -/

/-- `Im z_u ≠ 0` from a uniform lower bound. -/
theorem im_zt_ne_zero_of_le {Ev η u : ℝ} (hη : 0 < η) (h : η ≤ |(zt Ev u).im|) :
    (zt Ev u).im ≠ 0 := by
  have hlt := lt_of_lt_of_le hη h
  exact fun h0 => by simp [h0] at hlt

/-- On a window ending strictly before `1` the spectral parameter stays off the real axis,
with the explicit `η = (1 - u₁) Im m_E`. -/
theorem le_abs_im_zt_of_le {Ev : ℝ} (hE : |Ev| < 2) {u₁ : ℝ} (hu₁ : u₁ < 1) {u : ℝ}
    (hu : u ≤ u₁) : (1 - u₁) * (mE Ev).im ≤ |(zt Ev u).im| := by
  have hm := mE_im_pos hE
  have h1 : (0 : ℝ) < 1 - u₁ := by linarith
  have h2 : (0 : ℝ) < 1 - u := by linarith
  have hzu : (zt Ev u).im = (1 - u) * (mE Ev).im := zt_im Ev u
  have hpos : 0 < (zt Ev u).im := by rw [hzu]; positivity
  rw [abs_of_pos hpos, hzu]
  exact mul_le_mul_of_nonneg_right (by linarith) hm.le

end Gauss

end RBM

