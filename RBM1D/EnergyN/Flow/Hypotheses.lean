/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Flow.EnergyUniform

/-!
# The Steps 1–4 flow predicates at an `N`-dependent energy

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, §2.7.

The four predicates of the flow argument that Steps 1, 2 and 4 of §2.7 use, at an `N`-dependent
energy `E : ℕ → ℝ`.

## Main declarations

* `RBM.AprioriFlowN`, `RBM.LocalLawFlowN`, `RBM.AprioriDecayFlowN`, `RBM.SharpLmKFlowN` — the
  `N`-dependent-energy forms of (2.73), (2.75), (2.76), (2.78)/(2.79).

## The energy

None of the four predicates here fixes an energy-dependent constant (they only consume such a
bound), so no κ-bound is needed in this file.
-/

namespace RBM

open MeasureTheory Filter

section HypothesesN

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B)

/-- **(2.73)** (Step 1), at an `N`-dependent energy: `|L_{u,σ,a}| ≺ (ℓ_u/ℓ_s)^{n-1}
(W ℓ_u η_u)^{-n+1}`, uniformly in `u ∈ [s,t]`. -/
def AprioriFlowN (E : ℕ → ℝ) (s t : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → StochDom B.P
    (fun N (p : TimeIcc s t N × LoopData (B.L N) n) ω => ‖X.Lval (E N) N p.1 ω p.2.idx‖)
    (fun N p _ => (B.ell N p.1 / B.ell N (s N)) ^ (n - 1) * (B.scale (E N) N p.1)⁻¹ ^ (n - 1))

/-- **(2.75)** (Step 2), at an `N`-dependent energy: `‖G_u - m‖_max ≺ (W ℓ_u η_u)^{-1/2}`,
uniformly in `u ∈ [s,t]`. -/
def LocalLawFlowN (E : ℕ → ℝ) (s t : ℕ → ℝ) : Prop :=
  StochDom B.P
    (fun N (p : TimeIcc s t N × (B.Idx N × B.Idx N)) ω => X.llErr (E N) N p.1 ω p.2)
    (fun N p _ => (B.scale (E N) N p.1)⁻¹ ^ ((1 : ℝ) / 2))

/-- **(2.76)** (Step 2), at an `N`-dependent energy: for `σ = (+,-)`, `|L_u - K_u| ≺ (η_s/η_u)^4
(W ℓ_u η_u)^{-2} (exp(-(|a₁-a₂|/ℓ_u)^{1/2}) + W^{-D})`. -/
def AprioriDecayFlowN (E : ℕ → ℝ) (s t : ℕ → ℝ) : Prop :=
  ∀ D : ℝ, 0 < D → StochDom B.P
    (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
      X.lkErr (E N) N p.1 ω (pmLoop p.2.1 p.2.2))
    (fun N p _ => (etaT (E N) (s N) / etaT (E N) p.1) ^ 4 * (B.scale (E N) N p.1)⁻¹ ^ 2 *
      B.decayProf N p.1 D p.2.1 p.2.2)

/-- **(2.78)/(2.79)** (Step 4/5), at an `N`-dependent energy: `max_{σ,a} |L_{u,σ,a} - K_{u,σ,a}| ≺
(W ℓ_u η_u)^{-n}`, uniformly in `u ∈ [s,t]`. -/
def SharpLmKFlowN (E : ℕ → ℝ) (s t : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → StochDom B.P
    (fun N (p : TimeIcc s t N × LoopData (B.L N) n) ω => X.lkErr (E N) N p.1 ω p.2.idx)
    (fun N p _ => (B.scale (E N) N p.1)⁻¹ ^ n)

variable {X}

end HypothesesN

end RBM
