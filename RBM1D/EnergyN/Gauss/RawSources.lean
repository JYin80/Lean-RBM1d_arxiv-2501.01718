/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.RawSources
import RBM1D.EnergyN.Gauss.EntryBoundTime
import RBM1D.EnergyN.Hierarchy.Step1
import RBM1D.Flow.EnergyUniformReg

/-!
# The raw sources of the moving local law, at an `N`-dependent energy

Three statements at an `N`-dependent energy `E : ℕ → ℝ`: the source event `sourceGood` holds with
high probability (`RBM.RawSources.highProb_sourceGoodN`), and the source bounds on it, given the
hypotheses of Step 1 (`RBM.RawSources.general_moving_raw_sourcesN`) or with these built in the
proof (`RBM.RawSources.general_moving_raw_sources_of_scaleN`).

## The external `κ`

The theorems take an external `κ` via `hE : ∀ N, |E N| ≤ 2 - κ` and pass it directly into
`Step1.aprioriN` / `step1Hyp_gauss_of_scale''N` (`Gauss/EntryBoundTime.lean`); no `κ` is derived
from `2 - |E N|`. `general_moving_raw_sourcesN` fixes no energy-dependent constant itself: it
takes `κ` through `highProb_sourceGoodN`. The energy-free helpers `measurableSet_sourceGood`,
`sourceGood_subset_normGood`, `sourceEvent_on_sourceGood`, `rawThree_on_sourceGood`
(deterministic per fixed `(E, N)`) and the generic (`E`-free) `Gauss.highProb_norm_Xmat_le` are
applied at `E N`.
-/

namespace RBM.RawSources

open Filter MeasureTheory Set Gauss Step2Bootstrap CutHypTheta

noncomputable section

/-- **The source event `sourceGood` holds with high probability**, from (2.68)–(2.70) at `s`, the
regime condition and the hypotheses of Step 1. The margin is the external `κ` of `hE`. -/
theorem highProb_sourceGoodN (d : Dims) {E : ℕ → ℝ} {κ c : ℝ} {s t : ℕ → ℝ}
    (hκ0 : 0 < κ) (hE : ∀ N, |E N| ≤ 2 - κ) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hc : 0 < c) (hreg : Cond272NReg (band d) E s t c)
    (hB : BoundsCoreN (sample d) E s)
    (hStep : Step1.HypN (sample d) E s t)
    {ζ : ℝ} (hζ : 0 < ζ) :
    HighProb (P d) (fun N => sourceGood d (E N) s t ζ N) := by
  have h3 := Step1.aprioriN (sample d) hκ0 hE hB hs0 hst ht1
    hreg.1 hc hreg.2 hStep 3 (by norm_num)
  have h4 := Step1.aprioriN (sample d) hκ0 hE hB hs0 hst ht1
    hreg.1 hc hreg.2 hStep 4 (by norm_num)
  have h6 := Step1.aprioriN (sample d) hκ0 hE hB hs0 hst ht1
    hreg.1 hc hreg.2 hStep 6 (by norm_num)
  have hp3 : HighProb (P d) (fun N => rawEvent d (E N) s t ζ 3 N) := h3.highProb hζ
  have hp4 : HighProb (P d) (fun N => rawEvent d (E N) s t ζ 4 N) := h4.highProb hζ
  have hp6 : HighProb (P d) (fun N => rawEvent d (E N) s t ζ 6 N) := h6.highProb hζ
  change HighProb (P d) (fun N =>
    (((normGood d N ∩ rawEvent d (E N) s t ζ 3 N) ∩
      rawEvent d (E N) s t ζ 4 N) ∩ rawEvent d (E N) s t ζ 6 N))
  exact (((Gauss.highProb_norm_Xmat_le d).inter hp3).inter hp4).inter hp6

/-- **The source bounds**: for every `ζ > 0`, `sourceGood` holds with high probability, is
measurable and contained in `normGood`, and on it, eventually, the source event
`FullQuadVar.SourceEvent` and the bound `|L_{u,3}| ≤ sourceC3` hold at all `u ∈ [s, t]`. It takes
the external `κ` through `highProb_sourceGoodN`. -/
theorem general_moving_raw_sourcesN (d : Dims) {E : ℕ → ℝ} {κ c : ℝ} {s t : ℕ → ℝ}
    (hκ0 : 0 < κ) (hE : ∀ N, |E N| ≤ 2 - κ) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hc : 0 < c) (hreg : Cond272NReg (band d) E s t c)
    (hB : BoundsCoreN (sample d) E s)
    (hStep : Step1.HypN (sample d) E s t) :
    ∀ ζ : ℝ, 0 < ζ →
      HighProb (P d) (fun N => sourceGood d (E N) s t ζ N) ∧
      (∀ N, MeasurableSet (sourceGood d (E N) s t ζ N)) ∧
      (∀ N, sourceGood d (E N) s t ζ N ⊆ normGood d N) ∧
      ∀ᶠ N : ℕ in atTop,
        ∀ ω ∈ sourceGood d (E N) s t ζ N,
        ∀ u : TimeIcc s t N,
          FullQuadVar.SourceEvent (sample d) (E N) N (u : ℝ) ω
            (sourceEll d s ζ N) (sourceC4 d (E N) s ζ N u) ∧
          (∀ p : LoopData (d.L N) 3,
            ‖(sample d).Lval (E N) N (u : ℝ) ω p.idx‖ ≤ sourceC3 d (E N) s ζ N u) := by
  have hE2 : ∀ N, |E N| < 2 := fun N => by linarith [hE N]
  intro ζ hζ
  refine ⟨highProb_sourceGoodN d hκ0 hE hs0 hst ht1 hc hreg hB hStep hζ,
    fun N => measurableSet_sourceGood d (hE2 N) ht1 ζ N,
    fun N => sourceGood_subset_normGood d (E N) s t ζ N, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with N hN ω hω u
  exact ⟨sourceEvent_on_sourceGood d (hE2 N) hs0 ht1 hζ (by omega) u hω,
    rawThree_on_sourceGood d u hω⟩

/-- **The source bounds without the hypotheses of Step 1**, which are built from the same
assumptions through `step1Hyp_gauss_of_scale''N`, with the external `κ` of `hE`. -/
theorem general_moving_raw_sources_of_scaleN (d : Dims) {E : ℕ → ℝ} {κ c : ℝ}
    {s t : ℕ → ℝ} (hκ0 : 0 < κ) (hE : ∀ N, |E N| ≤ 2 - κ) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hc : 0 < c) (hreg : Cond272NReg (band d) E s t c)
    (hB : BoundsCoreN (sample d) E s) :
    ∀ ζ : ℝ, 0 < ζ →
      HighProb (P d) (fun N => sourceGood d (E N) s t ζ N) ∧
      (∀ N, MeasurableSet (sourceGood d (E N) s t ζ N)) ∧
      (∀ N, sourceGood d (E N) s t ζ N ⊆ normGood d N) ∧
      ∀ᶠ N : ℕ in atTop,
        ∀ ω ∈ sourceGood d (E N) s t ζ N,
        ∀ u : TimeIcc s t N,
          FullQuadVar.SourceEvent (sample d) (E N) N (u : ℝ) ω
            (sourceEll d s ζ N) (sourceC4 d (E N) s ζ N u) ∧
          (∀ p : LoopData (d.L N) 3,
            ‖(sample d).Lval (E N) N (u : ℝ) ω p.idx‖ ≤ sourceC3 d (E N) s ζ N u) := by
  have hStep : Step1.HypN (sample d) E s t :=
    step1Hyp_gauss_of_scale''N d hκ0 hE hB hs0 hst ht1 hreg.1 hc hreg.2
  exact general_moving_raw_sourcesN d hκ0 hE hs0 hst ht1 hc hreg hB hStep

section Compat

end Compat

end
end RBM.RawSources
