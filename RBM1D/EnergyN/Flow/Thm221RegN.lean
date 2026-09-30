/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Flow.EnergyUniformReg

/-!
# Theorem 2.21 with (2.71), at an `N`-dependent energy

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, §2.7.

`RBM.Thm221NReg` (`RBM.Cond272NReg`, with `RBM.BoundsN` in and out), its bridge
`RBM.Thm221NReg.toThm221N'`, and the corollary `RBM.BoundsN_of_Thm221NReg`. `RBM.Cond272NReg`
(`Flow/EnergyUniformReg.lean`) and `RBM.BoundsN` (`Flow/EnergyUniform.lean`) are the
`N`-dependent-energy forms this structure needs.

The quantifier order of `RBM.Thm221NReg` is that of `RBM.Thm221NoELNReg`
(`Flow/EnergyUniformReg.lean`): `κ`, then `E : ℕ → ℝ` with `∀ N, |E N| ≤ 2 - κ`, then `c`, then
`s, t`, with every `∀ᶠ N` inside the step condition.

## Main declarations

* `RBM.Thm221NReg` — Theorem 2.21 with (2.71), `N`-dependent energy, `Reg` step condition.
* `RBM.Thm221NReg.toThm221N'` — into `RBM.Thm221N'`.
* `RBM.BoundsN_of_Thm221NReg` — Lemmas 2.18–2.20 with (2.71), from `RBM.Thm221NReg`, at an
  `N`-dependent energy: `BoundsNInput d κ` is one line from `RBM.thm221RegN_gauss d hκ`.
-/

namespace RBM

open MeasureTheory Filter

section Thm221RegN

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- **Theorem 2.21 with (2.71)**, `N`-dependent energy, `Reg` step condition. -/
structure Thm221NReg (X : Sample B) (κ : ℝ) : Prop where
  step : ∀ E : ℕ → ℝ, (∀ N, |E N| ≤ 2 - κ) → ∀ c : ℝ, 0 < c → ∀ s t : ℕ → ℝ,
    (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) → (∀ N, t N < 1) → Cond272NReg B E s t c →
    BoundsN X E s → BoundsN X E t

/-- The regime form implies the gained form at an `N`-dependent energy, so everything
already proved from `RBM.Thm221N'` (`Flow/EnergyUniform.lean`) holds from `RBM.Thm221NReg`. -/
theorem Thm221NReg.toThm221N' {X : Sample B} {κ : ℝ} (hκ : 0 < κ) (hT : Thm221NReg X κ) :
    Thm221N' X κ where
  step E hE c hc0 s t hs0 hst ht1 hcond hB :=
    hT.step E hE c hc0 s t hs0 hst ht1
      (hcond.toCond272NReg (fun N => by linarith [hE N]) hst ht1 hc0.le) hB

/-- **Lemmas 2.18–2.20 from `RBM.Thm221NReg`, at an `N`-dependent energy**:
`RBM.BoundsN X E t` for every `t` with `N ^ (-1 + τ) ≤ 1 - t N` eventually. `BoundsNInput d κ` is
`RBM.boundsNInput_of_Thm221NReg hκ (RBM.thm221RegN_gauss d hκ)` in one line. -/
theorem BoundsN_of_Thm221NReg {X : Sample B} {E : ℕ → ℝ} {κ : ℝ} (hκ : 0 < κ)
    (hT : Thm221NReg X κ) (hE : ∀ N, |E N| ≤ 2 - κ) {τ : ℝ} (hτ : 0 < τ) {t : ℕ → ℝ}
    (ht0 : ∀ N, 0 ≤ t N) (ht : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-1 + τ) ≤ 1 - t N) :
    BoundsN X E t :=
  BoundsN_of_Thm221N' X hκ (hT.toThm221N' hκ) hE hτ ht0 ht

end Thm221RegN

end RBM
