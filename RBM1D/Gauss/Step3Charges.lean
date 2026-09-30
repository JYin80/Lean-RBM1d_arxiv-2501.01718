/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Step2Close

/-!
# The `2`-loop by charges: the `(+,+)` input isolated

Formalization support for Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, (5.76) and Lemma 5.11
(`n = 2`).

The bound on `Ξ^{(L-K)}_{u,2}` of (5.76) is a maximum over **all four** charges
`σ ∈ {+,-}²`.  Of these, `(+,-)` and `(-,+)` are already `≺ A_s^{1/2}` from Steps 1–2 alone,
and `(-,-)` is the complex conjugate of `(+,+)` (a deterministic identity).  The remaining input
is `(+,+)` — Lemma 5.11 at `n = 2`.  This file supplies the charge-level bookkeeping of that
split.

## Main results

* `RBM.Sample.lkMaxSigma`, `RBM.Sample.xiLKSigma`, `RBM.Step3.flowXiLKSigma` — the `2`-loop
  restricted to a single fixed charge `(σ₁,σ₂)`, reusing `RBM.Sample.lkMax`/`RBM.Sample.xiLK`'s
  pattern (`RBM.loopMax`'s companion at the charge level).
* `RBM.Step3.flowXiLKTwoPM` — the `2`-loop restricted to `σ ∈ {(+,-),(-,+)}`.
* `RBM.Sample.lkMax_two_eq_max4` — **`lkMax` at loop length `2` is the max over the four
  charges**, the Lean form of (5.76)'s definition as a maximum over `σ ∈ {+,-}²`.
* `RBM.Sample.lkMaxSigma_conj` — the `(-,-)` `2`-loop equals the `(+,+)` one, per sample (a
  deterministic identity from `RBM.ChargeReduce.lkErr_two_const`).
* `RBM.Step3.flowXiLK_two_eq_max_pp_twoPM` — `flowXiLK` at `n = 2` is
  `max(Ξ_{(+,+)}, flowXiLKTwoPM)`.
* `RBM.StochDom.max` — the union bound for a pointwise maximum.
-/

noncomputable section

namespace RBM

open MeasureTheory Filter

/-! ### The `2`-loop restricted to a single charge -/

namespace Sample

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B)

/-- The `2`-loop restricted to the single charge `(σ₁,σ₂)`:
`max_{a,b} |L_{t,(σ₁,σ₂),(a,b)} - K_{t,(σ₁,σ₂),(a,b)}|`, the per-charge summand of (5.76)
(the companion of `RBM.Sample.lkMax` at `m = 2`, restricted to one of the four charges). -/
noncomputable def lkMaxSigma (E : ℝ) (N : ℕ) (t : ℝ) (ω : Ω) (σ₁ σ₂ : Bool) : ℝ :=
  ⨆ ab : ZMod (B.L N) × ZMod (B.L N), X.lkErr E N t ω ⟨[σ₁, σ₂], [ab.1, ab.2]⟩

/-- The charge-restricted `Ξ^{(L-K)}_{t,(σ₁,σ₂)}`. -/
noncomputable def xiLKSigma (E : ℝ) (N : ℕ) (t : ℝ) (ω : Ω) (σ₁ σ₂ : Bool) : ℝ :=
  X.lkMaxSigma E N t ω σ₁ σ₂ * B.scale E N t ^ 2

variable {E : ℝ} {N : ℕ} {t : ℝ} {ω : Ω}

theorem le_lkMaxSigma (σ₁ σ₂ : Bool) (a b : ZMod (B.L N)) :
    X.lkErr E N t ω ⟨[σ₁, σ₂], [a, b]⟩ ≤ X.lkMaxSigma E N t ω σ₁ σ₂ :=
  le_ciSup (f := fun ab : ZMod (B.L N) × ZMod (B.L N) =>
    X.lkErr E N t ω ⟨[σ₁, σ₂], [ab.1, ab.2]⟩) (Set.finite_range _).bddAbove (a, b)

theorem lkMaxSigma_le_lkMax (σ₁ σ₂ : Bool) :
    X.lkMaxSigma E N t ω σ₁ σ₂ ≤ X.lkMax E N t ω 2 := by
  refine ciSup_le fun ab => ?_
  set v : LoopData (B.L N) 2 := (![σ₁, σ₂], ![ab.1, ab.2]) with hv
  have hidx : v.idx = (⟨[σ₁, σ₂], [ab.1, ab.2]⟩ : LoopIdx (ZMod (B.L N))) := by
    simp [hv, LoopData.idx, List.ofFn_succ]
  rw [← hidx]
  exact X.lkErr_le_lkMax v

/-- **`lkMax` at loop length `2` is the max over the four charges** — the charge decomposition
of (5.76)'s `Ξ^{(L-K)}_{t,2} = max_{σ,a} …`. -/
theorem lkMax_two_eq_max4 :
    X.lkMax E N t ω 2 =
      max (max (X.lkMaxSigma E N t ω true true) (X.lkMaxSigma E N t ω true false))
        (max (X.lkMaxSigma E N t ω false true) (X.lkMaxSigma E N t ω false false)) := by
  refine le_antisymm (ciSup_le fun v => ?_)
    (max_le (max_le (X.lkMaxSigma_le_lkMax true true) (X.lkMaxSigma_le_lkMax true false))
      (max_le (X.lkMaxSigma_le_lkMax false true) (X.lkMaxSigma_le_lkMax false false)))
  have hidx : v.idx = (⟨[v.1 0, v.1 1], [v.2 0, v.2 1]⟩ : LoopIdx (ZMod (B.L N))) := by
    simp [LoopData.idx, List.ofFn_succ]
  rw [hidx]
  have hle : X.lkErr E N t ω ⟨[v.1 0, v.1 1], [v.2 0, v.2 1]⟩
      ≤ X.lkMaxSigma E N t ω (v.1 0) (v.1 1) :=
    X.le_lkMaxSigma (v.1 0) (v.1 1) (v.2 0) (v.2 1)
  cases h0 : v.1 0 <;> cases h1 : v.1 1 <;> rw [h0, h1] at hle
  · exact hle.trans (le_max_of_le_right (le_max_right _ _))
  · exact hle.trans (le_max_of_le_right (le_max_left _ _))
  · exact hle.trans (le_max_of_le_left (le_max_right _ _))
  · exact hle.trans (le_max_of_le_left (le_max_left _ _))

/-- **Conjugation swaps the two constant charges**, at the level of the charge-restricted
`lkMax`: `RBM.ChargeReduce.lkErr_two_const` summed over `(a,b)`. A deterministic identity — no
bound on `(+,+)` is used or needed. -/
theorem lkMaxSigma_conj (hE : |E| ≤ 2) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    X.lkMaxSigma E N t ω false false = X.lkMaxSigma E N t ω true true := by
  unfold Sample.lkMaxSigma
  congr 1
  funext ab
  exact ChargeReduce.lkErr_two_const X hE N ht0 ht1 ω ab.1 ab.2

/-- The four-charge decomposition folds to `max(pp, max(pm,mp))` once `mm = pp`
(`RBM.Sample.lkMaxSigma_conj`). -/
theorem lkMax_two_eq_max_pp_twoPM (hE : |E| ≤ 2) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    X.lkMax E N t ω 2 = max (X.lkMaxSigma E N t ω true true)
      (max (X.lkMaxSigma E N t ω true false) (X.lkMaxSigma E N t ω false true)) := by
  rw [X.lkMax_two_eq_max4, X.lkMaxSigma_conj hE ht0 ht1,
    max_comm (X.lkMaxSigma E N t ω false true) (X.lkMaxSigma E N t ω true true),
    max_max_max_comm (X.lkMaxSigma E N t ω true true) (X.lkMaxSigma E N t ω true false)
      (X.lkMaxSigma E N t ω true true) (X.lkMaxSigma E N t ω false true),
    max_self]

/-- The scaled (`Ξ^{(L-K)}`) form of `lkMax_two_eq_max_pp_twoPM`. -/
theorem xiLK_two_eq_max_pp_twoPM (hE : |E| ≤ 2) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    X.xiLK E N t ω 2 = max (X.xiLKSigma E N t ω true true)
      (max (X.xiLKSigma E N t ω true false) (X.xiLKSigma E N t ω false true)) := by
  have hs2 : (0 : ℝ) ≤ B.scale E N t ^ 2 := sq_nonneg _
  unfold Sample.xiLK Sample.xiLKSigma
  rw [X.lkMax_two_eq_max_pp_twoPM hE ht0 ht1, max_mul_of_nonneg _ _ hs2,
    max_mul_of_nonneg _ _ hs2]

end Sample

/-! ### The charge-restricted `flowXiLK` families -/

namespace Step3

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- `Ξ^{(L-K)}_{u,(σ₁,σ₂)}` for `u ∈ [s,t]`: the charge-restricted family. -/
noncomputable def flowXiLKSigma (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) (σ₁ σ₂ : Bool) :
    ∀ N, TimeIcc s t N → Ω → ℝ := fun N u ω => X.xiLKSigma E N u ω σ₁ σ₂

/-- **`Ξ^{(L-K)}_{u,2}` restricted to `σ ∈ {(+,-),(-,+)}`**: `max(Ξ_{(+,-)}, Ξ_{(-,+)})`. Reuses
`flowXiLKSigma` (which reuses `RBM.Sample.lkMax`). -/
noncomputable def flowXiLKTwoPM (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) :
    ∀ N, TimeIcc s t N → Ω → ℝ :=
  fun N u ω => max (X.xiLKSigma E N u ω true false) (X.xiLKSigma E N u ω false true)

variable {E : ℝ} {s t : ℕ → ℝ}

/-- **`flowXiLK` at `n = 2` is `max(Ξ_{(+,+)}, flowXiLKTwoPM)`.** -/
theorem flowXiLK_two_eq_max_pp_twoPM (X : Sample B) (hE : |E| ≤ 2) (hs0 : ∀ N, 0 ≤ s N)
    (ht1 : ∀ N, t N < 1) :
    flowXiLK X E s t 2 = fun N u ω => max (flowXiLKSigma X E s t true true N u ω)
      (flowXiLKTwoPM X E s t N u ω) := by
  funext N u ω
  have hu0 : (0 : ℝ) ≤ (u : ℝ) := (hs0 N).trans u.2.1
  have hu1 : (u : ℝ) < 1 := u.2.2.trans_lt (ht1 N)
  exact X.xiLK_two_eq_max_pp_twoPM hE hu0 hu1

end Step3

/-! ### A bridge from a raw loopwise bound to `flowXiLKSigma`, and a union bound for `max` -/

/-- **The union bound for a pointwise maximum**: if `ξ₁ ≺ ζ` and `ξ₂ ≺ ζ` (the same `ζ`), then
`max(ξ₁,ξ₂) ≺ ζ`. -/
theorem StochDom.max {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {U : ℕ → Type*}
    {ξ₁ ξ₂ ζ : ∀ N, U N → Ω → ℝ} (h₁ : StochDom P ξ₁ ζ) (h₂ : StochDom P ξ₂ ζ) :
    StochDom P (fun N u ω => max (ξ₁ N u ω) (ξ₂ N u ω)) ζ := by
  refine StochDom.of_subset_union h₁ h₂ fun τ hτ => ⟨τ, hτ, Eventually.of_forall fun N => ?_⟩
  rintro ω ⟨u, hu⟩
  rw [lt_max_iff] at hu
  rcases hu with hu | hu
  · exact Or.inl ⟨u, hu⟩
  · exact Or.inr ⟨u, hu⟩

namespace Gauss

variable (d : Dims)

end Gauss

end RBM
