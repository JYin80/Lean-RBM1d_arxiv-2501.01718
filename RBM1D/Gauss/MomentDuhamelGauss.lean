/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.MomentDuhamel
import RBM1D.Gauss.LoopC2

/-!
# The Gaussian unloading of the moment Duhamel: joint `C²` of the resolvent

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.2: an analytic ingredient of (5.20) in moment form on the Gaussian flow
`H_u = √u • X`.

## Main results

* `RBM.Gauss.contDiffAt_resH_path` — **the `(z, M)`-joint `C²` regularity of the resolvent**,
  along an arbitrary `C²` spectral path, for instance the path `u ↦ z_u` of (2.33).
  `RBM.Gauss.BddC1On` is the *first-order*, set-localised class; what is needed here is
  second-order and joint, and it turns out not to need a new bounded class at all: the joint
  `C²` statement is `RBM.Gauss.contDiff_resH`'s proof with the pair `(u, M)` in place of `M`,
  because `(u, M) ↦ (M + Mᴴ)/2 - z_u` is already jointly `C²` and `Ring.inverse` is `C^∞` at
  units.  The spectral parameter `z_u = E + (1 - u) m_E` has `Im z_u → 0` as `u → 1`, so the
  statement is local in the time.

Nothing here is an `axiom` and nothing here is `sorry`.
-/

namespace RBM.Gauss

open MeasureTheory Filter
open scoped Matrix.Norms.L2Operator NNReal InnerProductSpace

variable {d : Dims} {N : ℕ} {Ψ : ℝ → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}

variable {T : Set ℝ}

/-! ### `(z, M)`-joint `C²` for the resolvent -/

section ResolventJoint

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The resolvent is jointly `C²` in `(time, matrix)` along a `C²` spectral path.**

`RBM.Gauss.BddC1On` is first-order
and set-localised; the second-order joint statement needs no new class, because
`RBM.Gauss.resH` is `Ring.inverse` applied to `(u, M) ↦ (M + Mᴴ)/2 - z_u`, which is already
jointly `C^∞` when `z` is `C²`, and `Ring.inverse` is `C^∞` at units. -/
theorem contDiffAt_resH_path {z : ℝ → ℂ} {u : ℝ} (hz : ContDiffAt ℝ 2 z u)
    (hzim : (z u).im ≠ 0) (M : Matrix n n ℂ) :
    ContDiffAt ℝ 2 (fun q : ℝ × Matrix n n ℂ => resH (z q.1) q.2) (u, M) := by
  have hsm : ContDiffAt ℝ 2 (fun q : ℝ × Matrix n n ℂ => z q.1 • (1 : Matrix n n ℂ)) (u, M) :=
    (hz.comp (u, M) contDiff_fst.contDiffAt).smul contDiffAt_const
  have hT : ContDiffAt ℝ 2
      (fun q : ℝ × Matrix n n ℂ => hermCLM n q.2 - z q.1 • (1 : Matrix n n ℂ)) (u, M) :=
    (((hermCLM n).contDiff.comp contDiff_snd).contDiffAt).sub hsm
  obtain ⟨v, hvs⟩ : ∃ v : (Matrix n n ℂ)ˣ,
      (v : Matrix n n ℂ) = hermCLM n M - z u • (1 : Matrix n n ℂ) :=
    ⟨(isUnit_resH_arg hzim M).unit, IsUnit.unit_spec _⟩
  have hg : ContDiffAt ℝ 2 (Ring.inverse (M₀ := Matrix n n ℂ))
      ((fun q : ℝ × Matrix n n ℂ => hermCLM n q.2 - z q.1 • (1 : Matrix n n ℂ)) (u, M)) := by
    show ContDiffAt ℝ 2 _ (hermCLM n M - z u • (1 : Matrix n n ℂ))
    rw [← hvs]
    exact contDiffAt_ringInverse ℝ v
  exact hg.comp (u, M) hT

end ResolventJoint

end RBM.Gauss
