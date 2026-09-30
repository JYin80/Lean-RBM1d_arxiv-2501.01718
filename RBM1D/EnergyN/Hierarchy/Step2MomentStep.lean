/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.Step2MomentStep
import RBM1D.EnergyN.Hierarchy.Step45

/-!
# The bound (5.48) of Step 2 at an `N`-dependent energy

`RBM.Step2MomentStep.flowEq548_of_near_farN`: the near-field and far-field bounds on `L - K` for
`σ = (+,-)` give (5.48) (`RBM.Step45.FlowEq548N`), at an `N`-dependent energy `E : ℕ → ℝ`.

No energy-dependent constant is fixed here: the proof is a one-line application of the generic,
`E`-free `RBM.Step2MomentStep.eq548_of_near_far`; the conclusion `RBM.Step45.FlowEq548N` unfolds
definitionally to the `Step45.Eq548 P ξ W ℓ η d pref` shape with `ξ, η, pref` eta-expanded at
`E N`.
-/

namespace RBM

namespace Step2MomentStep

/-- **(5.48) from the near-field and far-field bounds on `L - K`**, at an `N`-dependent
energy. -/
theorem flowEq548_of_near_farN {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B)
    {E : ℕ → ℝ} {s t : ℕ → ℝ}
    (hnear : ∀ D : ℝ, 0 < D → StochDom B.P
      (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
        X.lkErr (E N) N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => (etaT (E N) (s N) / etaT (E N) p.1) ^ 2 *
        tailT (B.W N : ℝ) (B.ell N p.1) (etaT (E N) p.1) D (zdist (B.L N) (p.2.1 - p.2.2))))
    (hfar : ∀ D : ℝ, 0 < D → StochDom B.P
      (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
        if (zdist (B.L N) (p.2.1 - p.2.2) : ℝ) ≤ 6 * ellStar (B.W N : ℝ) (B.ell N p.1)
          then 0 else X.lkErr (E N) N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => tailT (B.W N : ℝ) (B.ell N p.1) (etaT (E N) p.1) D
        (zdist (B.L N) (p.2.1 - p.2.2)))) :
    Step45.FlowEq548N X E s t := by
  refine eq548_of_near_far (fun N => by positivity) (fun N p => by positivity) hnear hfar

end Step2MomentStep

end RBM
