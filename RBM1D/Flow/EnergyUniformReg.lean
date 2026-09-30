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

/-!
# The energy-uniform `Reg` interface

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, §2.7, Theorem 2.21.

`RBM.Cond272NReg` is (2.72) as printed, at an `N`-dependent energy (`RBM.Cond272N`), together
with the regime bound `N^c ≤ W ℓ_t η_t`.  `RBM.Thm221NoELNReg` is Theorem 2.21 without (2.71), at
an `N`-dependent energy, with `RBM.Cond272NReg` as its step condition.

**This file is interface-only.**  It does *not* make any producer of `RBM.BoundsCoreN`
energy-uniform.  Nothing here claims `RBM.Thm221NoELNReg (sample d) κ` for any concrete `d`.

## Main declarations

* `RBM.Cond272NReg` — (2.72) at an `N`-dependent energy, plus the regime bound.
* `RBM.Thm221NoELNReg` — Theorem 2.21 without (2.71), `N`-dependent energy, `Reg` step
  condition.
* `RBM.Cond272N'.toCond272NReg` — the gained (2.72) implies `RBM.Cond272NReg`.
* `RBM.Thm221NoELNReg.toThm221NoELN'` — `RBM.Thm221NoELNReg` implies the gained form
  `RBM.Thm221NoELN'`.
* `RBM.BoundsCoreN_of_Thm221NoELNReg` — Lemmas 2.18–2.20 without (2.62), from
  `RBM.Thm221NoELNReg`, at an `N`-dependent energy.
-/

namespace RBM

open Filter

section EnergyUniformReg

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- (2.72) verbatim at an `N`-dependent energy, plus `N^c ≤ W ℓ_t η_t`. -/
def Cond272NReg (B : Band Ω) (E : ℕ → ℝ) (s t : ℕ → ℝ) (c : ℝ) : Prop :=
  Cond272N B E s t ∧ ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ B.scale (E N) N (t N)

/-- Theorem 2.21 without (2.71), `N`-dependent energy, `Reg` step condition. -/
structure Thm221NoELNReg (X : Sample B) (κ : ℝ) : Prop where
  step : ∀ E : ℕ → ℝ, (∀ N, |E N| ≤ 2 - κ) → ∀ c : ℝ, 0 < c → ∀ s t : ℕ → ℝ,
    (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) → (∀ N, t N < 1) → Cond272NReg B E s t c →
    BoundsCoreN X E s → BoundsCoreN X E t

/-- The gained `N`-dependent (2.72) implies `RBM.Cond272NReg`: it implies the printed (2.72)
(`RBM.Cond272N'.toCond272N`), and, since `(1 - s)/(1 - t) ≥ 1`, it gives `N^c ≤ W ℓ_t η_t`. -/
theorem Cond272N'.toCond272NReg {E : ℕ → ℝ} {s t : ℕ → ℝ} (hE : ∀ N, |E N| < 2)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 ≤ c)
    (h : Cond272N' B E s t c) : Cond272NReg B E s t c := by
  refine ⟨h.toCond272N hE hst ht1 hc0, ?_⟩
  filter_upwards [h] with N hN
  rw [etaT_div_etaT (hE N)] at hN
  have h1t : 0 < 1 - t N := by linarith [ht1 N]
  have h1s : 0 < 1 - s N := by linarith [hst N]
  have hR1 : (1 : ℝ) ≤ (1 - s N) / (1 - t N) := by
    rw [le_div_iff₀ h1t]; linarith [hst N]
  have hRp : (1 : ℝ) ≤ ((1 - s N) / (1 - t N)) ^ 30 := one_le_pow₀ hR1
  nlinarith [Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ)) c]

/-- `RBM.Thm221NoELNReg` implies its gained form `RBM.Thm221NoELN'`: a step that satisfies the
gained (2.72) satisfies `RBM.Cond272NReg` (`RBM.Cond272N'.toCond272NReg`). -/
theorem Thm221NoELNReg.toThm221NoELN' {X : Sample B} {κ : ℝ} (hκ : 0 < κ)
    (hT : Thm221NoELNReg X κ) : Thm221NoELN' X κ where
  step E hE c hc0 s t hs0 hst ht1 hcond hB :=
    hT.step E hE c hc0 s t hs0 hst ht1
      (hcond.toCond272NReg (fun N => by linarith [abs_nonneg (E N), hE N]) hst ht1 hc0.le) hB

/-- Lemmas 2.18–2.20 without (2.62), from `RBM.Thm221NoELNReg`, at an `N`-dependent energy: the
corollary of `RBM.BoundsCoreN_of_Thm221NoELN'` along `RBM.Thm221NoELNReg.toThm221NoELN'`. -/
theorem BoundsCoreN_of_Thm221NoELNReg {X : Sample B} {E : ℕ → ℝ} {κ : ℝ} (hκ : 0 < κ)
    (hT : Thm221NoELNReg X κ) (hE : ∀ N, |E N| ≤ 2 - κ) {τ : ℝ} (hτ : 0 < τ) {t : ℕ → ℝ}
    (ht0 : ∀ N, 0 ≤ t N) (ht : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-1 + τ) ≤ 1 - t N) :
    BoundsCoreN X E t :=
  BoundsCoreN_of_Thm221NoELN' X hκ (hT.toThm221NoELN' hκ) hE hτ ht0 ht

end EnergyUniformReg

namespace Band

variable {Ω : Type*} [MeasurableSpace Ω] (B : Band Ω)

end Band

section Satisfiable

end Satisfiable

end RBM
