/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.Step2
import RBM1D.Gauss.Envelope
import RBM1D.Gauss.Step2JStar

/-!
# Step 2 without the stopping time: the moment route

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, §5.3, along the **moment route** (no
Itô calculus, no martingales, and in particular **no optional stopping**).

The bootstrapped quantity is the **deterministic** function

  `φ_q(u) = E[(J*_{u,D})^q]`

instead of the random path `u ↦ J*_{u,D}`.  A deterministic function has no filtration, no
stopping time and no optional stopping theorem attached to it: once `φ_q` is *continuous* in
`u`, the argument of §5.3 is literally continuous induction, and the stopping time (5.43) is
replaced by a sup-of-a-closed-set argument.  The threshold keeps an `N^δ`-type margin, because
`≺` still has to beat an `N^τ` loss; continuous induction removes the stopping time, not the
margin.

## Main results

* `RBM.Step2Moment.one_le_jS` — `1 ≤ J*_{u,D}`; in particular `J*` is non-negative.
-/

namespace RBM

namespace Step2Moment

open MeasureTheory Filter

/-! ### Continuous induction with a varying threshold -/

section Bootstrap

end Bootstrap

/-! ### The moment `φ_q(u) = E[(J*_{u,D})^q]` -/

section Phi

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

variable (X : Sample B) {E D : ℝ} {s : ℕ → ℝ}

/-- `1 ≤ J*_{u,D}` (`RBM.Step2.one_le_jStar`); in particular `J*` is non-negative. -/
theorem one_le_jS (N : ℕ) (u : ℝ) (ω : Ω) : 1 ≤ Step2.jS X E D N u ω := by
  have hW : (0 : ℝ) < B.W N := by exact_mod_cast B.W_pos N
  exact Step2.one_le_jStar hW fun _ => norm_nonneg _

end Phi

/-! ### From moments to `≺`, uniformly in `u ∈ [s_N, t_N]`: the net of (5.46) -/

section Net

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]

end Net

/-! ### The inputs of the moment route -/

section Hyp

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

variable (X : Sample B) {E D : ℝ} {s t : ℕ → ℝ}

end Hyp

/-! ### The bootstrap -/

section Main

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E D : ℝ} {s t : ℕ → ℝ}

end Main

/-! ### (2.76) and Step 2 -/

section Conclusions

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}

end Conclusions

end Step2Moment

end RBM
