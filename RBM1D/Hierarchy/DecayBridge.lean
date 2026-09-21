/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.Decay
import RBM1D.Hierarchy.SumZeroDyn
import RBM1D.Hierarchy.Step1

/-!
# T118: the bridge between Lemma 5.9 (T59) and `RBM.SumZeroDyn.LKDecay` (T60)

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random
Band Matrices*, §5.4, Lemma 5.9 (5.75).

`RBM1D/Hierarchy/SumZeroDyn.lean:62` records that `RBM.Decay.lemma59` "does not plug into"
`RBM.SumZeroDyn.LKDecay`, because the former holds *on the event of Lemma 4.1* while the
latter is a `≺` statement uniform in `u ∈ [s, t]`.  This file shows that this is **not a
mismatch of statements**: the paper's (5.75) *is* a probability bound, so `LKDecay` is the
faithful side, and `Decay.lemma59` is its deterministic core (an explicitly documented
deviation of `Hierarchy/Decay.lean`).  What is missing is neither a reshaping of `LKDecay`
nor a reshaping of `lemma59`, but the **wrapper** that `Hierarchy/Decay.lean`'s own
"Deviations" section already names: "the passage to *with probability* `1 - O(W^{-D'})` is
the high-probability statement of that event".

That wrapper is `RBM.DecayBridge.lkDecay_of_highProb`.  It reduces `LKDecay` to a *pathwise,
purely deterministic* statement — membership in `RBM.DecayBridge.LKDecayEvent` — holding with
high probability.  `RBM.DecayBridge.loopDecay_lk_of_event` then exhibits `Decay.lemma59` as a
statement about exactly that pathwise object: its conclusion is literally
`Decay.LoopDecay` of `u ↦ L_{u,σ,a} - K_{u,σ,a}` in the `Sample`/`Band` vocabulary
(`X.Lval - B.Kval`), no translation required.

So the remaining obligation on the `LKDecay` side is *only* quantitative: choose the
parameters of Lemma 4.1 and (2.76) so that the radius and the error of `lemma59` beat
`ℓ_u N^τ` and `N^{-D}`, and show that the resulting event has high probability.
`RBM.DecayBridge.mem_lkDecayEvent_of_loopDecay` is the (trivial) monotonicity step that
consumes those two inequalities.

Nothing here touches `Hierarchy/SumZeroDyn.lean` or `Hierarchy/Decay.lean`.

## Main results

* `RBM.DecayBridge.farInd_mul_le_of_loopDecay` — the shape translation: Definition 5.8 in the
  `LoopIdx` form (`Decay.LoopDecay`) gives the `farInd`-weighted pointwise bound that
  `SumZeroDyn.LKDecay` compares.
* `RBM.DecayBridge.LKDecayEvent`, `RBM.DecayBridge.lkDecay_of_highProb` — the lift
  "pathwise `(u, τ, D)` decay w.h.p. ⟹ `LKDecay`".
* `RBM.DecayBridge.mem_lkDecayEvent_of_loopDecay` — the parameter-matching step.
* `RBM.DecayBridge.loopDecay_lk_of_event` — `Decay.lemma59` read in the `Sample`/`Band`
  vocabulary; its conclusion is already about `L - K` of the flow.

## What is *not* bridged here (and why)

`RBM.SumZeroDyn.Lemma510` is **not** bridged.  Its subject matter is `H.F` and `H.EE`, two
unconstrained data fields of `RBM.SumZeroDyn.Hierarchy`; `Hierarchy/Decay.lean` proves (5.77)
for the *concrete* terms `couplingLen`, `primBil`, `eG`, `eTens`.  Closing that gap means
*defining* `F` and `EE`, which is T58's deliverable, not a restatement of either lemma.  See
the warning in `RBM1D/Gauss/DischargeBDG.lean`: `duhamel` can be satisfied by fiat, and
`Lemma510` is precisely what stops the fiat choice of `F`; weakening it would remove that
guard.
-/

namespace RBM

namespace DecayBridge

open MeasureTheory

/-! ### Definition 5.8 in the two shapes -/

section Pointwise

variable {L : ℕ}

/-- **The shape translation.**  `Decay.LoopDecay` (Definition 5.8 on `LoopIdx`) gives exactly
the `farInd`-weighted pointwise bound that `RBM.SumZeroDyn.LKDecay` compares: for a loop
datum `q = (σ, a)` of length `m`, `‖F_{σ,a}‖ · 1(∃ i j, ‖a_i - a_j‖ ≥ ℓ) ≤ δ`. -/
theorem farInd_mul_le_of_loopDecay {m : ℕ} {ℓ δ : ℝ} (hδ : 0 ≤ δ)
    {F : LoopIdx (ZMod L) → ℂ} (h : Decay.LoopDecay L m ℓ δ F) (q : LoopData L m) :
    ‖F q.idx‖ * SumZeroDyn.farInd L ℓ q.2 ≤ δ := by
  classical
  by_cases hq : ∃ i j, ℓ ≤ (zdist L (q.2 i - q.2 j) : ℝ)
  · obtain ⟨x, hx, y, hy, hxy⟩ := Decay.mem_ofFn_of_fastDecay L hq
    have hle : ‖F q.idx‖ ≤ δ :=
      h q.idx q.idx_wf (le_of_eq q.idx_length) x hx y hy hxy
    simpa [SumZeroDyn.farInd, hq] using hle
  · simpa [SumZeroDyn.farInd, hq] using hδ

end Pointwise

/-! ### The lift: pathwise decay with high probability ⟹ `LKDecay` -/

section Lift

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- **The pathwise content of Lemma 5.9 at the parameters `(m, τ, D)`**: for every
`u ∈ [s_N, t_N]`, the loop function `L_{u,σ,a} - K_{u,σ,a}` has `(ℓ_u N^τ, N^{-D})` decay on
loops of length `m` (Definition 5.8).  This is a deterministic statement about the sample
point `ω`; `RBM.Decay.lemma59` is exactly a theorem producing it. -/
def LKDecayEvent (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) (m : ℕ) (τ D : ℝ) (N : ℕ) : Set Ω :=
  {ω | ∀ u : TimeIcc s t N, Decay.LoopDecay (B.L N) m (B.ell N (u : ℝ) * (N : ℝ) ^ τ)
        ((N : ℝ) ^ (-D)) (fun I => X.Lval E N (u : ℝ) ω I - B.Kval E N (u : ℝ) I)}

variable {X : Sample B} {E : ℝ} {s t : ℕ → ℝ}

/-- **Parameter matching.**  If, pathwise, `L - K` decays at every `u ∈ [s_N, t_N]` with a
radius at most `ℓ_u N^τ` and an error at most `N^{-D}`, then `ω ∈ LKDecayEvent`. -/
theorem mem_lkDecayEvent_of_loopDecay {m N : ℕ} {τ D : ℝ} {ω : Ω}
    {R δ : TimeIcc s t N → ℝ}
    (h : ∀ u : TimeIcc s t N, Decay.LoopDecay (B.L N) m (R u) (δ u)
      (fun I => X.Lval E N (u : ℝ) ω I - B.Kval E N (u : ℝ) I))
    (hR : ∀ u : TimeIcc s t N, R u ≤ B.ell N (u : ℝ) * (N : ℝ) ^ τ)
    (hδ : ∀ u : TimeIcc s t N, δ u ≤ (N : ℝ) ^ (-D)) :
    ω ∈ LKDecayEvent X E s t m τ D N :=
  fun u => (h u).mono (B.L N) le_rfl (hR u) (hδ u)

/-- **The lift (5.75).**  If the pathwise decay of Lemma 5.9 holds with high probability at
every `(m, τ, D)`, then `RBM.SumZeroDyn.LKDecay` holds.

This is the whole of the "event vs `≺`" gap recorded at `Hierarchy/SumZeroDyn.lean:62`: the
`≺` side needs no reshaping, and neither does `RBM.Decay.lemma59`. -/
theorem lkDecay_of_highProb
    (h : ∀ m, 1 ≤ m → ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ),
      HighProb B.P (LKDecayEvent X E s t m τ D)) :
    SumZeroDyn.LKDecay X E s t := by
  intro m hm τ hτ D hD
  refine Step1.stochDom_of_highProb (fun N _ _ => Real.rpow_nonneg (Nat.cast_nonneg N) _) ?_
  refine (h m hm τ hτ D hD).mono (Filter.Eventually.of_forall fun N ω hω => ?_)
  intro p
  exact farInd_mul_le_of_loopDecay (Real.rpow_nonneg (Nat.cast_nonneg N) _) (hω p.1) p.2

end Lift

/-! ### Lemma 5.9 is already a statement about `L - K` of the flow -/

section Lemma59

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {X : Sample B} {E : ℝ}

/-- **`RBM.Decay.lemma59` in the `Sample`/`Band` vocabulary.**  No translation is involved:
`X.Lval` is `RBM.gloop` of `H_u` at `z_u` and `B.Kval` is `RBM.Kgen`, which are literally the
two functions in the conclusion of `RBM.Decay.lemma59`.  Hence the deterministic core of
Lemma 5.9 produces membership in `RBM.DecayBridge.LKDecayEvent` through
`mem_lkDecayEvent_of_loopDecay`, and `lkDecay_of_highProb` then produces `LKDecay`.

The hypotheses are those of Lemma 4.1 (`GoodEvent`, `LDERow`, `LDECol`) together with the
decay (2.76) of the `(+,-)` `2`-loops, at the sample point `ω` and the time `u`. -/
theorem loopDecay_lk_of_event {N : ℕ} {u : ℝ} {ω : Ω} (hE : |E| ≤ 2)
    (hz : (zt E u).im ≠ 0) {δ : ℝ} (hΩ : GoodEvent (X.G E N u ω) (mE E) δ) (hδ : δ ≤ 1 / 2)
    {Φ : ℝ} (hΦ1 : 1 ≤ Φ) (hΦδ : 36 * Φ * δ ^ 2 ≤ 1)
    (hLrow : LDERow (X.H N u ω) (X.G E N u ω) (Sblk (B.L N) (B.W N)) Φ)
    (hLcol : LDECol (X.H N u ω) (X.G E N u ω) (Sblk (B.L N) (B.W N)) Φ)
    {ℓ δ₂ : ℝ} (hℓ : 0 ≤ ℓ) (hδ₂ : 0 ≤ δ₂)
    (hdec : ∀ a b : ZMod (B.L N), ℓ ≤ (zdist (B.L N) (a - b) : ℝ) →
      Lre (X.H N u ω) (zt E u) a b ≤ δ₂)
    (hu0 : 0 ≤ u) (hu1 : u < 1) {m : ℕ} (hm : 1 ≤ m) :
    Decay.LoopDecay (B.L N) m (2 * m * (ℓ + 2))
      (27 * Φ * Real.sqrt δ₂ * max 1 |(zt E u).im|⁻¹ ^ m
        + Decay.cKdecay m (1 - u) * Real.exp (-(cor35Rate (1 - u) * (2 * m * (ℓ + 2)))))
      (fun I => X.Lval E N u ω I - B.Kval E N u I) :=
  (Decay.lemma59 (B.L N) (B.three_le_L N) (X.hermitian N u ω) hz (norm_mE hE) hΩ hδ hΦ1 hΦδ
    hLrow hLcol hℓ hδ₂ hdec (fun σ => (norm_mSigma hE σ).le) hu0 hu1 hm).2

end Lemma59

end DecayBridge

end RBM
