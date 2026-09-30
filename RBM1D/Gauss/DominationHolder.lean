/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Domination
import RBM1D.Flow.Hypotheses

/-!
# The union bound with an exceptional event, and the time net on an `N`-dependent interval

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, Definition 2.1 (i) and the time net
of (5.46).

The *uncountable* union over the time `u` in Definition 2.1 (i) is removed by an `N^{-C}` net.
For the Gaussian flow a modulus of continuity in the time is available only with high
probability.  The modulus that `RBM1D/Gauss/Model.lean` supplies is
```
‖H_u − H_{u'}‖ = |√u − √u'| ‖X‖        (`RBM.Gauss.norm_Hflow_sub`),
```
so for a resolvent functional the Hölder constant carries a factor `‖X‖`, which is **not**
bounded pointwise in `ω`.  This file provides the two ingredients of the net argument in that
setting.

Why the weakening is free: the failure event of Definition 2.1 (i) is covered by
```
badSet ⊆ (badSet ∩ Ξ) ∪ Ξᶜ,
```
the first piece is handled by the net, and `P(Ξᶜ) ≤ N^{-(D+1)}` by definition of `HighProb`.
This is `RBM.Gauss.stochDom_of_subset_highProb`, the high-probability analogue of
`RBM.StochDom.of_subset`.

## Main definitions

* `RBM.Gauss.netTime` — the net of (5.46) on the `N`-dependent interval `[s_N, t_N]`: the net
  of `RBM1D/Gauss/Domination.lean` shifted by `s_N` and clipped at `t_N`.

## Main results

* `RBM.Gauss.stochDom_of_subset_highProb` — the union bound `badSet ⊆ (badSet ∩ Ξ) ∪ Ξᶜ`.
* `RBM.Gauss.netTime_mem`, `RBM.Gauss.exists_netTime_close` — the net lies in `[s_N, t_N]`, and
  every time of `[s_N, t_N]` is within `T / m` of a net point, `m = netSize A N`.
-/

namespace RBM.Gauss

open Filter MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The union bound with an exceptional event -/

section Core

variable {P : Measure Ω} [IsFiniteMeasure P]

omit [IsFiniteMeasure P] in
/-- **`RBM.StochDom.of_subset` with an exceptional event.**  If the failure event of `ξ ≺ ζ`
is, *on a high-probability event* `Ξ`, eventually contained in the failure event of a
domination that is already known, then `ξ ≺ ζ`.

The cover is `badSet ⊆ (badSet ∩ Ξ) ∪ Ξᶜ`: the first piece is controlled by the known
domination at the level `D + 1`, the second by `HighProb` at the level `D + 1`, and
`2 N^{-(D+1)} ≤ N^{-D}` (`RBM.eventually_two_mul_rpow_le`). -/
theorem stochDom_of_subset_highProb {U V : ℕ → Type*} {ξ ζ : ∀ N, U N → Ω → ℝ}
    {ξ' ζ' : ∀ N, V N → Ω → ℝ} {Ξ : ℕ → Set Ω} (h : StochDom P ξ' ζ') (hΞ : HighProb P Ξ)
    (hsub : ∀ τ > (0 : ℝ), ∃ τ' > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      badSet ξ ζ τ N ∩ Ξ N ⊆ badSet ξ' ζ' τ' N) :
    StochDom P ξ ζ := by
  intro τ hτ D hD
  obtain ⟨τ', hτ', hs⟩ := hsub τ hτ
  filter_upwards [hs, h τ' hτ' (D + 1) (by linarith), hΞ (D + 1) (by linarith),
    eventually_two_mul_rpow_le D] with N h0 h1 h2 h3
  have hp : (0 : ℝ) ≤ (N : ℝ) ^ (-(D + 1)) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hcover : badSet ξ ζ τ N ⊆ (badSet ξ ζ τ N ∩ Ξ N) ∪ (Ξ N)ᶜ := by
    intro ω hω
    by_cases hΞω : ω ∈ Ξ N
    · exact Or.inl ⟨hω, hΞω⟩
    · exact Or.inr hΞω
  calc P (badSet ξ ζ τ N) ≤ P ((badSet ξ ζ τ N ∩ Ξ N) ∪ (Ξ N)ᶜ) := measure_mono hcover
    _ ≤ P (badSet ξ ζ τ N ∩ Ξ N) + P (Ξ N)ᶜ := measure_union_le _ _
    _ ≤ P (badSet ξ' ζ' τ' N) + P (Ξ N)ᶜ := add_le_add (measure_mono h0) le_rfl
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))) + ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))) :=
        add_le_add h1 h2
    _ = ENNReal.ofReal (2 * (N : ℝ) ^ (-(D + 1))) := by rw [← ENNReal.ofReal_add hp hp]; ring_nf
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := ENNReal.ofReal_le_ofReal h3

end Core

/-! ### The net of (5.46) on an `N`-dependent interval -/

section Net

/-- The `k`-th point of the uniform net of (5.46) on the **`N`-dependent** interval
`[s_N, t_N]`, whose length is at most `T`.  The net of `RBM1D/Gauss/Domination.lean` lives on a
fixed `[0, T]`; shifting it by `s_N` and clipping at `t_N` keeps it inside `[s_N, t_N]` without
assuming `s_N < t_N`. -/
noncomputable def netTime (s t : ℕ → ℝ) (T A : ℝ) (N : ℕ) (k : Fin (netSize A N + 1)) : ℝ :=
  min (t N) (s N + netPt T A N k)

theorem netTime_mem {s t : ℕ → ℝ} (hst : ∀ N, s N ≤ t N) {T : ℝ} (hT : 0 ≤ T) (A : ℝ) (N : ℕ)
    (k : Fin (netSize A N + 1)) : netTime s t T A N k ∈ Set.Icc (s N) (t N) := by
  refine ⟨le_min (hst N) ?_, min_le_left _ _⟩
  have := (netPt_mem_Icc hT A N k).1
  linarith

/-- Every time of `[s_N, t_N]` is within `T / m` of a net point, `m = netSize A N`. -/
theorem exists_netTime_close {s t : ℕ → ℝ} {T : ℝ} (hT : 0 < T) (hlen : ∀ N, t N - s N ≤ T)
    (A : ℝ) (N : ℕ) {u : ℝ} (hu : u ∈ Set.Icc (s N) (t N)) :
    ∃ k, |u - netTime s t T A N k| ≤ T / (netSize A N : ℝ) := by
  have hmem : u - s N ∈ Set.Icc (0 : ℝ) T :=
    ⟨by linarith [hu.1], by linarith [hu.2, hlen N]⟩
  obtain ⟨k, hk⟩ := exists_netPt_close hT A N hmem
  refine ⟨k, ?_⟩
  have hkq : |u - (s N + netPt T A N k)| ≤ T / (netSize A N : ℝ) := by
    have h : u - (s N + netPt T A N k) = u - s N - netPt T A N k := by ring
    rw [h]; exact hk
  unfold netTime
  rcases le_or_gt (s N + netPt T A N k) (t N) with h | h
  · rwa [min_eq_right h]
  · rw [min_eq_left h.le]
    refine le_trans ?_ hkq
    rw [abs_of_nonpos (by linarith [hu.2]), abs_of_nonpos (by linarith [hu.2])]
    linarith

end Net

/-! ### The net theorem with a modulus valid only with high probability -/

section Uniform

variable {P : Measure Ω} [IsFiniteMeasure P]

end Uniform

/-! ### The net theorem with a `≺`-controlled Hölder constant -/

section RandomConstant

variable {P : Measure Ω} [IsFiniteMeasure P]

end RandomConstant

section SlowControl

variable {P : Measure Ω} [IsFiniteMeasure P]

end SlowControl

end RBM.Gauss

