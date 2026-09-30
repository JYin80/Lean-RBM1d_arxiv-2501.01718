/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Step6Sample
import RBM1D.Flow.EnergyUniform

/-!
# The (2.71) half of the induction step at an `N`-dependent energy

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, §2.7.

`RBM.bounds_of_boundsCore_of_sharpExpectN`: (2.68)–(2.71) at `t` from (2.68)–(2.70) at `t` and
(2.80) on `[s, t]`, at an `N`-dependent energy `E : ℕ → ℝ`. No energy-dependent constant is fixed
here: it uses the conclusion of Step 6 (`UnifDetDom (X.expErr …) …`) and
`RBM.BoundsCoreN`/`RBM.BoundsN` (`Flow/EnergyUniform.lean`).
-/

namespace RBM

section AssemblyN

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {X : Sample B} {E : ℕ → ℝ} {s t : ℕ → ℝ}

/-- **(2.68)–(2.71) at `t` from (2.68)–(2.70) at `t` and (2.80) on `[s,t]`, at an `N`-dependent
energy.** -/
theorem bounds_of_boundsCore_of_sharpExpectN (hBC : BoundsCoreN X E t)
    (hSE : UnifDetDom
      (fun N (p : TimeIcc s t N × LoopData (B.L N) 2) => X.expErr (E N) N p.1 p.2.idx)
      (fun N _ => (B.scale (E N) N (t N))⁻¹ ^ 3))
    (hst : ∀ N, s N ≤ t N) : BoundsN X E t where
  toBoundsCoreN := hBC
  expect := hSE.precomp_param fun N u => (TimeIcc.last hst N, u)

end AssemblyN

end RBM
