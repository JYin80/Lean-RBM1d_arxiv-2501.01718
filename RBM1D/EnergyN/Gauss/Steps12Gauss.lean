/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Flow.Hypotheses
import RBM1D.Gauss.Step2Gauss

/-!
# The conclusions of Steps 1–2 at an `N`-dependent energy

The structure `RBM.Steps12N`: the conclusions (2.73)–(2.76) of Steps 1 and 2 of §2.7, at an
`N`-dependent energy `E : ℕ → ℝ`, with the fields `apriori`, `weakLaw`, `localLaw`,
`aprioriDecay`. No energy-dependent constant is fixed here. The Gaussian pipeline produces it by
`RBM.Gauss.steps12_gauss_plainN` (`RBM1D/EnergyN/Gauss/Step2Gauss.lean`).
-/

namespace RBM

open MeasureTheory Filter

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- **The conclusions of Steps 1–2 of §2.7**, (2.73)–(2.76), at an `N`-dependent energy. -/
structure Steps12N (X : Sample B) (E : ℕ → ℝ) (s t : ℕ → ℝ) : Prop where
  /-- **(2.73)** (Step 1): `|L_{u,σ,a}| ≺ (ℓ_u/ℓ_s)^{n-1} (W ℓ_u η_u)^{-n+1}`. -/
  apriori : ∀ n : ℕ, 1 ≤ n → StochDom B.P
    (fun N (p : TimeIcc s t N × LoopData (B.L N) n) ω => ‖X.Lval (E N) N p.1 ω p.2.idx‖)
    (fun N p _ => (B.ell N p.1 / B.ell N (s N)) ^ (n - 1) * (B.scale (E N) N p.1)⁻¹ ^ (n - 1))
  /-- **(2.74)** (Step 1): `‖G_u - m‖_max ≺ (W ℓ_u η_u)^{-1/4}`. -/
  weakLaw : StochDom B.P
    (fun N (p : TimeIcc s t N × (B.Idx N × B.Idx N)) ω => X.llErr (E N) N p.1 ω p.2)
    (fun N p _ => (B.scale (E N) N p.1)⁻¹ ^ ((1 : ℝ) / 4))
  /-- **(2.75)** (Step 2): `‖G_u - m‖_max ≺ (W ℓ_u η_u)^{-1/2}`. -/
  localLaw : StochDom B.P
    (fun N (p : TimeIcc s t N × (B.Idx N × B.Idx N)) ω => X.llErr (E N) N p.1 ω p.2)
    (fun N p _ => (B.scale (E N) N p.1)⁻¹ ^ ((1 : ℝ) / 2))
  /-- **(2.76)** (Step 2): for `σ = (+,-)`, `|L_u - K_u| ≺ (η_s/η_u)^4 (W ℓ_u η_u)^{-2}
  (exp(-(|a₁-a₂|/ℓ_u)^{1/2}) + W^{-D})`. -/
  aprioriDecay : ∀ D : ℝ, 0 < D → StochDom B.P
    (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
      X.lkErr (E N) N p.1 ω (pmLoop p.2.1 p.2.2))
    (fun N p _ => (etaT (E N) (s N) / etaT (E N) p.1) ^ 4 * (B.scale (E N) N p.1)⁻¹ ^ 2 *
      B.decayProf N p.1 D p.2.1 p.2.2)

end RBM
