/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Step3Charges

/-!
# `Ξ^{(L-K)}` for fixed charges at an `N`-dependent energy

`RBM.stochDom_flowXiLKSigmaN`: `Ξ^{(L-K)}` for the charges `(σ₁, σ₂)` from a bound on
`|L - K|_{(σ₁,σ₂)}`, at an `N`-dependent energy `E : ℕ → ℝ`. No energy-dependent constant is fixed
here: there is no bound on `E` among the hypotheses (only a `B.scale`-nonnegativity fact and a
`StochDom` hypothesis), and the proof never uses `mE`/`etaT`/any energy-dependent constant.

`RBM.Step3.flowXiLKSigma` is a `def` at a single `E : ℝ`; it is used at `E N` as
`fun N => Step3.flowXiLKSigma X (E N) s t σ₁ σ₂ N` (definitionally
`X.xiLKSigma (E N) N u ω σ₁ σ₂` once applied, by unfolding `flowXiLKSigma`/`xiLKSigma`).
-/

noncomputable section

namespace RBM

open MeasureTheory Filter

/-- **`Ξ^{(L-K)}_{(σ₁,σ₂)} ≺ f_u (W ℓ_u η_u)^2`** from `|L - K|_{(σ₁,σ₂)} ≺ f_u`. No
energy-dependent constant is fixed here, and no energy hypothesis is needed. -/
theorem stochDom_flowXiLKSigmaN {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E : ℕ → ℝ}
    {s t : ℕ → ℝ} (X : Sample B) {σ₁ σ₂ : Bool} {f : ∀ N, TimeIcc s t N → ℝ}
    (hA : ∀ N (u : TimeIcc s t N), 0 ≤ B.scale (E N) N u)
    (h : StochDom B.P
      (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
        X.lkErr (E N) N p.1 ω ⟨[σ₁, σ₂], [p.2.1, p.2.2]⟩)
      (fun N p _ => f N p.1)) :
    StochDom B.P (fun N => Step3.flowXiLKSigma X (E N) s t σ₁ σ₂ N)
      (fun N u _ => f N u * B.scale (E N) N u ^ 2) := by
  refine StochDom.of_subset_union h h fun τ hτ => ⟨τ, hτ, Eventually.of_forall fun N => ?_⟩
  rintro ω ⟨u, hu⟩
  by_cases h' : ∃ p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N)),
      (N : ℝ) ^ τ * f N p.1 < X.lkErr (E N) N p.1 ω ⟨[σ₁, σ₂], [p.2.1, p.2.2]⟩
  · exact Or.inl h'
  · exfalso
    have hall : ∀ ab : ZMod (B.L N) × ZMod (B.L N),
        X.lkErr (E N) N u ω ⟨[σ₁, σ₂], [ab.1, ab.2]⟩ ≤ (N : ℝ) ^ τ * f N u :=
      fun ab => not_lt.1 fun hc => h' ⟨(u, ab), hc⟩
    have hmax : X.lkMaxSigma (E N) N u ω σ₁ σ₂ ≤ (N : ℝ) ^ τ * f N u := ciSup_le hall
    have hApow : (0 : ℝ) ≤ B.scale (E N) N u ^ 2 := pow_nonneg (hA N u) _
    have hgoal : Step3.flowXiLKSigma X (E N) s t σ₁ σ₂ N u ω
        ≤ (N : ℝ) ^ τ * (f N u * B.scale (E N) N u ^ 2) := by
      change X.lkMaxSigma (E N) N u ω σ₁ σ₂ * B.scale (E N) N u ^ 2 ≤ _
      calc X.lkMaxSigma (E N) N u ω σ₁ σ₂ * B.scale (E N) N u ^ 2
          ≤ ((N : ℝ) ^ τ * f N u) * B.scale (E N) N u ^ 2 :=
            mul_le_mul_of_nonneg_right hmax hApow
        _ = (N : ℝ) ^ τ * (f N u * B.scale (E N) N u ^ 2) := by ring
    exact absurd hu (not_lt.2 hgoal)

section Compat

end Compat

end RBM
