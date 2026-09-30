/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Flow.Thm221Bare
import RBM1D.Flow.EnergyUniform
import RBM1D.Hierarchy.ChargeReduce
import RBM1D.Gauss.MomentDuhamel
import RBM1D.Gauss.CutoffBounds
import RBM1D.Hierarchy.Step2MomentStep
import RBM1D.EnergyN.Flow.Hypotheses

/-!
# (2.68)–(2.70) from the flow, at an `N`-dependent energy

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, §2.7 (the remark after the six steps).

`RBM.BoundsCore_of_flowN`: (2.68)–(2.70) at `t` from Steps 2, 4, 5, at an `N`-dependent energy
`E : ℕ → ℝ`. It uses `RBM.LocalLawFlowN`, `RBM.SharpLmKFlowN`
(`RBM1D/EnergyN/Flow/Hypotheses.lean`) and `RBM.BoundsCoreN` (`Flow/EnergyUniform.lean`). No
energy-dependent constant is fixed here.
-/

namespace RBM

open MeasureTheory Filter

section Thm221NoELN

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {X : Sample B} {E : ℕ → ℝ} {s t : ℕ → ℝ}

/-- **(2.68)–(2.70) at `t` from (2.75), (2.78) and (2.79)**, at an `N`-dependent energy. -/
theorem BoundsCore_of_flowN (hst : ∀ N, s N ≤ t N) (hll : LocalLawFlowN X E s t)
    (hLmK : SharpLmKFlowN X E s t)
    (hdec : ∀ D : ℝ, 0 < D → StochDom B.P
      (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
        X.lkErr (E N) N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => (B.scale (E N) N p.1)⁻¹ ^ 2 * B.decayProf N p.1 D p.2.1 p.2.2)) :
    BoundsCoreN X E t where
  LmK n hn := (hLmK n hn).precomp_param fun N u => (TimeIcc.last hst N, u)
  decay D hD := (hdec D hD).precomp_param fun N a => (TimeIcc.last hst N, a)
  localLaw := hll.precomp_param fun N ij => (TimeIcc.last hst N, ij)

end Thm221NoELN

end RBM
