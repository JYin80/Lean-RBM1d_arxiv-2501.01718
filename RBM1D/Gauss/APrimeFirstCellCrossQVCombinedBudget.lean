/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellMinkowskiExact

/-!
# T499: the actual first-cell full-cross and QV numerical budget

The two terms are literally the `B` and `g` used by T494's Minkowski
consumer.  T469 pays the full-cross integral and T487 pays the square root
of the actual uncut QV integral, on the identical sharp common event.
The multiplier of the full-cross integral is exactly `2`.
-/

namespace RBM.APrimeFirstCellCrossQVCombinedBudget

open Filter MeasureTheory Set Gauss CutHypTheta
open APrimeFirstCellMinkowskiExact (endpoint weight B g)

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

noncomputable abbrev delta : ℝ := APrimeFirstCellMinkowskiExact.delta

/-- The two public QV modules use the identical moving endpoint. -/
theorem endpoint_eq_qv (N k : ℕ) :
    endpoint N k = APrimeFirstCellQVNormBudget.endpoint N k := rfl

/-- The T494 weight is T487's canonical weight without any change of moment order. -/
theorem weight_eq_qv (τ' : ℝ) (p N k : ℕ) :
    weight τ' p N k = APrimeFirstCellQVNormBudget.weight τ' p N k := rfl

/-- The rate in the actual Minkowski consumer is the uncut T487 rate. -/
theorem g_eq_qv (τ' : ℝ) (p N k : ℕ) (a : LoopArg (d.L N) 2) (r : ℝ) :
    g τ' p N k a r = APrimeFirstCellQVNormBudget.g τ' p N k a r := rfl

/-- The exact sum of the cross and QV contributions at one moving output. -/
def combinedBudgetAt (τ' α β : ℝ) (p N k : ℕ)
    (a : LoopArg (d.L N) 2) : Prop :=
  2 * (∫ r in (0 : ℝ)..endpoint N k, B τ' α p N k r) +
      Real.sqrt ((2 * (p : ℝ) - 1) *
        (∫ r in (0 : ℝ)..endpoint N k, g τ' p N k a r)) ≤
    2 * (APrimeFirstCellFullCrossBudget.budgetConstant p *
      APrimeFirstCellFullCrossBudget.crossScale α N (endpoint N k)) +
    Real.sqrt (2 * (p : ℝ) - 1) *
      (384 * Real.sqrt 3 * (N : ℝ) ^ (α / 2) *
          APrimeFirstCellLoopCap.xRate (endpoint N k) ^ (-(2 : ℝ)) +
        Real.sqrt (endpoint N k) * (N : ℝ) ^ (-β / 2))

/-- The moment order and both exponents are fixed before the eventual size;
the estimate is uniform over all active mesh endpoints and outputs. -/
def actualCrossQVCombinedBudget (τ' α β : ℝ) (p : ℕ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∀ k : ℕ, 1 ≤ k →
    k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N →
    ∀ a : LoopArg (d.L N) 2, combinedBudgetAt τ' α β p N k a

/-- Both public estimates consume high probability of this same literal
event; no second parameter or event is chosen. -/
theorem eventually_combinedBudgetAt_of_highProb {τ' α β : ℝ}
    (hτ' : 0 < τ') (hα : 0 < α) (hβ : 0 < β)
    (p : ℕ) (hp : 1 ≤ p)
    (hΞ : HighProb (P d)
      (APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' delta α)) :
    actualCrossQVCombinedBudget τ' α β p := by
  have hcross := APrimeFirstCellFullCrossBudget.eventually_integral_literalBfull_le
    hτ' hα hΞ p hp
  have hnorm := APrimeFirstCellQVNormBudget.eventually_actualQVNormBudget_of_highProb
    hτ' hα hp hβ hΞ
  have hint := APrimeFirstCellQVNormBudget.eventually_actualQVIntegralBudget
    hτ' hβ hp hnorm
  have hqv := APrimeFirstCellQVNormBudget.eventually_actualQVSqrtExplicitBudget
    hτ' hp hint
  filter_upwards [hcross, hqv] with N hcrossN hqvN
  intro k hk1 hk a
  have hB :
      (∫ r in (0 : ℝ)..endpoint N k, B τ' α p N k r) ≤
        APrimeFirstCellFullCrossBudget.budgetConstant p *
          APrimeFirstCellFullCrossBudget.crossScale α N (endpoint N k) :=
    hcrossN k hk
  have hG :
      Real.sqrt ((2 * (p : ℝ) - 1) *
        (∫ r in (0 : ℝ)..endpoint N k, g τ' p N k a r)) ≤
      Real.sqrt (2 * (p : ℝ) - 1) *
        (384 * Real.sqrt 3 * (N : ℝ) ^ (α / 2) *
            APrimeFirstCellLoopCap.xRate (endpoint N k) ^ (-(2 : ℝ)) +
          Real.sqrt (endpoint N k) * (N : ℝ) ^ (-β / 2)) :=
    hqvN k hk1 hk a
  exact add_le_add (mul_le_mul_of_nonneg_left hB (by norm_num)) hG

/-- The literal cross and QV integrals both vanish at the empty prefix. -/
theorem zero_prefix_integrals (τ' α : ℝ) (p N : ℕ)
    (a : LoopArg (d.L N) 2) :
    endpoint N 0 = 0 ∧
    (∫ r in (0 : ℝ)..endpoint N 0, B τ' α p N 0 r) = 0 ∧
    (∫ r in (0 : ℝ)..endpoint N 0, g τ' p N 0 a r) = 0 := by
  simp [endpoint, cutNetPt_zero]

/-- The exact sum, including its square-root coefficient, is zero for `k = 0`. -/
theorem combinedContribution_k_zero (τ' α : ℝ) (p N : ℕ)
    (a : LoopArg (d.L N) 2) :
    2 * (∫ r in (0 : ℝ)..endpoint N 0, B τ' α p N 0 r) +
      Real.sqrt ((2 * (p : ℝ) - 1) *
        (∫ r in (0 : ℝ)..endpoint N 0, g τ' p N 0 a r)) = 0 := by
  obtain ⟨_, hB, hg⟩ := zero_prefix_integrals τ' α p N a
  rw [hB, hg]
  simp

/-- The same numerical bound is valid at `k = 0`, for every size. -/
theorem combinedBudgetAt_k_zero (τ' α β : ℝ) (p N : ℕ)
    (a : LoopArg (d.L N) 2) : combinedBudgetAt τ' α β p N 0 a := by
  unfold combinedBudgetAt
  rw [combinedContribution_k_zero]
  have hv : endpoint N 0 = 0 := (zero_prefix_integrals τ' α p N a).1
  have hx : APrimeFirstCellLoopCap.xRate (endpoint N 0) = 1 := by
    rw [hv]
    norm_num [APrimeFirstCellLoopCap.xRate, etaT, mE]
  apply add_nonneg
  · exact mul_nonneg (by norm_num)
      (mul_nonneg (APrimeFirstCellFullCrossBudget.budgetConstant_nonneg p)
        (APrimeFirstCellFullCrossBudget.crossScale_nonneg (by rw [hv]; norm_num)))
  · rw [hx]
    positivity

/-- A positive `k = 2` resident of the identical sharp event carries the
literal canonical weight and the combined budget for every output. -/
def positiveTwoCombinedResident (τ' α β : ℝ) (p : ℕ) : Prop :=
  ∀ᶠ N : ℕ in atTop,
    ∃ ω ∈ APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' delta α N,
      endpoint N 0 = 0 ∧
      0 < endpoint N 2 ∧
      endpoint N 2 ≤ firstCellT τ' N ∧
      2 ≤ cutNetTop (fun _ => 0) (firstCellT τ')
        APrimeSmoothTransition.transitionMesh N ∧
      weight τ' p N 2 ω = 1 ∧
      ∀ a : LoopArg (d.L N) 2, combinedBudgetAt τ' α β p N 2 a

theorem positiveTwoCombinedResident_of_inputs {τ' α β : ℝ} {p : ℕ}
    (hresident : APrimeFirstCellCanonicalPlateau.positiveCanonicalSharpPlateau
      τ' delta α)
    (hbudget : actualCrossQVCombinedBudget τ' α β p) :
    positiveTwoCombinedResident τ' α β p := by
  filter_upwards [hresident, hbudget] with N hresidentN hbudgetN
  obtain ⟨ω, hω, hk, hweight, hv0, hvT, _hrest⟩ := hresidentN
  refine ⟨ω, hω, ?_, hv0, hvT, hk, hweight p, ?_⟩
  · simp [endpoint, cutNetPt_zero]
  · intro a
    exact hbudgetN 2 (by norm_num) hk a

theorem eventually_sharpCommonEvent_nonempty {τ' α β : ℝ} {p : ℕ}
    (hresident : positiveTwoCombinedResident τ' α β p) :
    ∀ᶠ N : ℕ in atTop,
      (APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' delta α N).Nonempty := by
  filter_upwards [hresident] with N hN
  obtain ⟨ω, hω, _⟩ := hN
  exact ⟨ω, hω⟩

/-- Closed numerical producer with one measurable HighProb event, exact
empty-prefix identities, and a positive same-event canonical resident. -/
theorem exists_combinedBudget_with_resident :
    ∃ τ' : ℝ, 0 < τ' ∧
      ∀ α : ℝ, 0 < α → ∀ p : ℕ, 1 ≤ p → ∀ β : ℝ, 0 < β →
        (∀ N, MeasurableSet
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' delta α N)) ∧
        HighProb (P d)
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' delta α) ∧
        actualCrossQVCombinedBudget τ' α β p ∧
        (∀ N, ∀ a : LoopArg (d.L N) 2,
          combinedBudgetAt τ' α β p N 0 a) ∧
        (∀ᶠ N : ℕ in atTop,
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' delta α N).Nonempty) ∧
        positiveTwoCombinedResident τ' α β p := by
  obtain ⟨τ', hτ', hall⟩ :=
    APrimeFirstCellCanonicalPlateau.exists_sharpCommonEvent_with_canonical_plateau
  refine ⟨τ', hτ', ?_⟩
  intro α hα p hp β hβ
  obtain ⟨hmeas, hprob, hresident⟩ := hall delta
    APrimeFirstCellFarRowAbsorb.delta_pos
    (by norm_num [delta, APrimeFirstCellMinkowskiExact.delta,
      APrimeFirstCellMomFlowDerivExact.delta, APrimeFirstCellHcrossExact.delta,
      APrimeFirstCellJointCrossActual.delta, APrimeFirstCellFarRowAbsorb.delta]) α hα
  have hbudget := eventually_combinedBudgetAt_of_highProb hτ' hα hβ p hp hprob
  have htwo := positiveTwoCombinedResident_of_inputs hresident hbudget
  exact ⟨hmeas, hprob, hbudget,
    fun N a => combinedBudgetAt_k_zero τ' α β p N a,
    eventually_sharpCommonEvent_nonempty htwo, htwo⟩

#print axioms endpoint_eq_qv
#print axioms weight_eq_qv
#print axioms g_eq_qv
#print axioms eventually_combinedBudgetAt_of_highProb
#print axioms zero_prefix_integrals
#print axioms combinedContribution_k_zero
#print axioms combinedBudgetAt_k_zero
#print axioms positiveTwoCombinedResident_of_inputs
#print axioms eventually_sharpCommonEvent_nonempty
#print axioms exists_combinedBudget_with_resident

end

end RBM.APrimeFirstCellCrossQVCombinedBudget
