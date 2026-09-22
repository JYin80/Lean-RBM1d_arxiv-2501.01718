/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Flow.Thm221NoEL
import RBM1D.Gauss.Eq45Flow
import RBM1D.Flow.Step1Producer

/-!
# The `hΘ` and `Eq45Flow` slots of the main chain — the producers and the wiring (T243)

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, Lemma 5.11 at `n = 2` (p. 65) and Lemma 4.1 (4.5) (p. 48).

T239's hypothesis table for `RBM.thm221NoEL_of_inputs_entries` has six slots.  This file
closes the **third** and the **fifth**:

| # | slot in T239's table | after this file |
|---|---|---|
| 3 | `hΘ`: `Ξ^{(L-K)}_{u,2} ≺ (W ℓ_s η_s)^{1/2}` | **gone** — from a `CutHypEv` |
| 5 | `RBM.StepGlue.Eq45Flow` | **gone** — from the three (4.5) inputs |

## Step 0 inventory (the ticket's first task)

**`hΘ` = `RBM.StochDom B.P (RBM.Step3.flowXiLK X E s t 2) (fun N _ _ => A_s^{1/2})`.**

| what feeds it | supplier | status before this file |
|---|---|---|
| `xiLK_two_le` needs a `BootPP` | `MomentDuhamelCut.bootPP_of_cutHyp` | takes a `CutHyp` |
| same conclusion, no `BootPP` | `MomentDuhamelCut.stochDom_of_cutHypEv` | a `CutHypEv` |
| `hΘ1 : ∀ᶠ N, 1 ≤ A_s^{1/2}` | — | **missing**; proved here from (2.72) |
| `hinit : Ξ^{(L-K)}_{s,2} ≺ 1` | `Step2PP.xiLK_two_init` + `BoundsCore.LmK` | no `hB` in scope |

The last row is the whole reason slot 3 had no producer: `RBM.thm221NoEL_of_inputs_W` asks for
`hΘ` under `|E| ≤ 2 - κ`, `0 ≤ s ≤ t < 1` and `RBM.Cond272Reg` only, while the initial bound
`Ξ^{(L-K)}_{s,2} ≺ 1` is `RBM.BoundsCore X E s` — available one level down, at
`RBM.boundsCore_step_of_inputs_reg_W`, and thrown away on the way up.  This is exactly the
"free strengthening" T239 flagged for `Eq548EntryData.init`; `thm221NoEL_of_inputs_step345`
below performs it for slot 3.

**`RBM.StepGlue.Eq45Flow`.**

| what feeds it | supplier | status before this file |
|---|---|---|
| the transfer itself | `RBM.Gauss.eq45Flow_of_inputs` (T121) | present, **general `X`** |
| `RBM.Gauss.IBPFlow x` | `RBM.Gauss.ibpFlow_of_unifDom` (T124, Gaussian) | present |
| `RBM.Gauss.FlucRowFlow x` | `RBM.Gauss.flucRowFlow_of_gain'` (T124, Gaussian) | present |
| `RBM.Gauss.FlucBlkFlow x` | `RBM.Gauss.flucBlkFlow_of_gain'` (T124, Gaussian) | present |

So slot 5 needed no new mathematics at all — only the existential over the auxiliary field `x`
(`RBM.Eq45FlowInputs`) and the wiring, both here.

## Main definitions

* `RBM.Eq45FlowInputs` — the three time-indexed inputs of (4.5), with the auxiliary field
  `x N u ω i` ("`E_i(G_u(ii) - m)`") existentially quantified.

## Main results

* `RBM.eventually_one_le_flowAs_rpow_half`, `RBM.xiLK_two_init_of_boundsCore` — the two side
  conditions of the bootstrap, **proved**, not assumed.
* `RBM.flow_hTheta_of_cutHypEv`, `RBM.flow_hTheta_of_cutHyp` — **slot 3**.
* `RBM.eq45Flow_of_eq45FlowInputs` — **slot 5**.
* `RBM.boundsCore_step_of_inputs_step345`, `RBM.thm221NoEL_of_inputs_step345` — the chain with
  both slots replaced by their producers' inputs.
* `RBM.thm221NoEL_of_inputs_step345_conclusion_unchanged` (`rfl`) — the conclusion did not move.

## Satisfiability (compiled, §5)

* `RBM.step345_threshold_one_le` — the slot-3 threshold `A_s^{1/2}` is `≥ 1`, so the interface
  is *not* asking for `Ξ^{(L-K)}_{u,2} ≪ 1`, which `hinit` could never support.
* `RBM.step345_theta_left_endpoint` — the slot-3 *conclusion*, read at the left endpoint
  `u = s_N`, already follows from `RBM.BoundsCore`, i.e. the request is consistent with the
  data the chain carries in.  It is therefore not a request that contradicts slot 6.
* `RBM.flucRowFlow_canonical`, `RBM.flucBlkFlow_canonical` — at the explicit choice
  `x N u ω i = G_u(ii) - m` **two of the three fields of `RBM.Eq45FlowInputs` hold for every
  sample and every model**, so the bundle's three fields are not jointly contradictory, and
  `RBM.eq45FlowInputs_of_ibpFlow_canonical` reduces the bundle to a single statement.
* `RBM.eq45FlowInputs_nonfiat` — the bundle **implies** (4.5), `|L - K|_1 ≺ L^max`, for *every*
  choice of `x`, so no `x` can empty all three conjuncts at once.
  ⚠ That single statement is *not* weaker than the triple at the paper's `x`: at
  `x = G_{ii} - m` the surviving `RBM.Gauss.IBPFlow` is the self-consistent equation with
  error `≺ L^max ≍ Ψ²`, which is the whole content of §4.  The reduction is recorded as a
  non-vacuity witness, **not** as the route to take.

## Deviations from the paper

**None new.**  Both producers are wirings of statements already in the repository; neither
changes a statement's mathematical content.  Two bookkeeping points, recorded for the audit:

* `RBM.Eq45FlowInputs` is the existential closure of `RBM.Gauss.IBPFlow`,
  `RBM.Gauss.FlucRowFlow`, `RBM.Gauss.FlucBlkFlow` over `x`.  Those three are p. 50's
  integration-by-parts display and (4.12) with the time moved inside the index set of `≺`
  (T121's delta, already recorded).
* `thm221NoEL_of_inputs_step345` demands its slot-3 input under the **extra** premise
  `RBM.BoundsCore X E s`.  That weakens the hypothesis (an extra premise on an assumed
  implication), so the theorem is stronger than `RBM.thm221NoEL_of_inputs_W` at that slot; the
  conclusion `RBM.Thm221NoEL X κ` is byte-identical.

§§6–8 (T245) add no deviation either.  One point belongs on the record, because it is the
one thing in the merged table that is *not* a free strengthening: slots 3 and 5 ask for
`RBM.MomentDuhamelCut.CutHypEv` and `RBM.Eq45FlowInputs`, which **imply** the hypotheses they
replace (`RBM.flow_hTheta_of_cutHypEv`, `RBM.eq45Flow_of_eq45FlowInputs`) rather than following
from them.  They are therefore different, stronger requests, licensed by having producers, and
`RBM.thm221NoEL_of_inputs_merged_slots_imply_old` states all three slot-wise implications in
one place so the direction cannot be misread.  Slot 1 and the three changes inside slot 6 *are*
free (`RBM.Gauss.step1Hyp_slot` adds no hypothesis; `RBM.Eq548EntryData.toEv` compiles).
-/

namespace RBM

open MeasureTheory Filter

section Slot3

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E : ℝ} {s t : ℕ → ℝ}

/-- **The slot-3 threshold is at least `1`** (for large `N`): `1 ≤ (W ℓ_s η_s)^{1/2}`, from
(2.72) through `RBM.Step3.scales_flow`.  This is `hΘ1` of
`RBM.MomentDuhamelCut.stochDom_of_cutHypEv`. -/
theorem eventually_one_le_flowAs_rpow_half (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hcond : Cond272 B E s t) :
    ∀ᶠ N : ℕ in atTop, (1 : ℝ) ≤ Step3.flowAs B E s N ^ ((1 : ℝ) / 2) := by
  filter_upwards [(Step3.scales_flow (E := E) (s := s) (t := t) hE hs0 hst ht1 hcond).one_le_As]
    with N hN
  exact Real.one_le_rpow hN (by norm_num)

/-- **`hinit`**: `Ξ^{(L-K)}_{s,2} ≺ 1`, from (2.68) at `n = 2`.  This is
`RBM.Step2PP.xiLK_two_init` fed by `RBM.BoundsCore.LmK`; it is the field of `RBM.BoundsCore`
that the `hΘ` slot of `RBM.thm221NoEL_of_inputs_W` could not see. -/
theorem xiLK_two_init_of_boundsCore (X : Sample B) (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hB : BoundsCore X E s) :
    StochDom B.P (fun N (_ : Unit) ω => X.xiLK E N (s N) ω 2) (fun _ _ _ => (1 : ℝ)) :=
  Step2PP.xiLK_two_init X hE hs0 hst ht1 (hB.LmK 2 (by norm_num))

/-- **Slot 3 of T239's table, produced.**

`hΘ : Ξ^{(L-K)}_{u,2} ≺ (W ℓ_s η_s)^{1/2}` uniformly in `u ∈ [s,t]`, from

* the truncated moment Duhamel interface `RBM.MomentDuhamelCut.CutHypEv` for
  `Ξ^{(L-K)}_{·,2}` at the threshold `(W ℓ_s η_s)^{1/2}` — the same interface that supplies
  slot 2, and the object `RBM.MomentDuhamelCut.bootPP_of_cutHyp` was built for;
* (2.72), which gives `1 ≤ (W ℓ_s η_s)^{1/2}`;
* (2.68) at `n = 2`, which gives the bootstrap's initial condition.

The last two are **theorems** here, so what is left of slot 3 is the `CutHypEv` alone. -/
theorem flow_hTheta_of_cutHypEv (X : Sample B) (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hcond : Cond272 B E s t)
    (hB : BoundsCore X E s)
    (H : MomentDuhamelCut.CutHypEv B.P (fun N u ω => X.xiLK E N u ω 2) s t
      (fun N => Step3.flowAs B E s N ^ ((1 : ℝ) / 2))) :
    StochDom B.P (Step3.flowXiLK X E s t 2)
      (fun N (_ : TimeIcc s t N) (_ : Ω) => Step3.flowAs B E s N ^ ((1 : ℝ) / 2)) := by
  have := B.isProbabilityMeasure
  exact MomentDuhamelCut.stochDom_of_cutHypEv H
    (eventually_one_le_flowAs_rpow_half hE hs0 hst ht1 hcond)
    (xiLK_two_init_of_boundsCore X hE hs0 hst ht1 hB)

/-- `flow_hTheta_of_cutHypEv` at the older, `∀ N` interface `RBM.MomentDuhamelCut.CutHyp`. -/
theorem flow_hTheta_of_cutHyp (X : Sample B) (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hcond : Cond272 B E s t)
    (hB : BoundsCore X E s)
    (H : MomentDuhamelCut.CutHyp B.P (fun N u ω => X.xiLK E N u ω 2) s t
      (fun N => Step3.flowAs B E s N ^ ((1 : ℝ) / 2))) :
    StochDom B.P (Step3.flowXiLK X E s t 2)
      (fun N (_ : TimeIcc s t N) (_ : Ω) => Step3.flowAs B E s N ^ ((1 : ℝ) / 2)) :=
  flow_hTheta_of_cutHypEv X hE hs0 hst ht1 hcond hB (MomentDuhamelCut.CutHypEv.of_cutHyp H)

end Slot3

section Slot5

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E : ℝ} {s t : ℕ → ℝ}

/-- **The three time-indexed inputs of (4.5)**, with the auxiliary field `x` existentially
quantified.  `x N u ω i` stands for `E_i(G_u(ii) - m)`, the conditional expectation of the
diagonal Green entry; the three conjuncts are p. 50's integration-by-parts display and the two
instances of the fluctuation averaging (4.12) that Lemma 4.1 uses, each with the time `u` inside
the index set of `≺` (`RBM.Gauss.IBPFlow`, `RBM.Gauss.FlucRowFlow`, `RBM.Gauss.FlucBlkFlow`). -/
def Eq45FlowInputs (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) : Prop :=
  ∃ x : ∀ N, TimeIcc s t N → Ω → B.Idx N → ℂ,
    Gauss.IBPFlow X E s t x ∧ Gauss.FlucRowFlow X E s t x ∧ Gauss.FlucBlkFlow X E s t x

/-- **Slot 5 of T239's table, produced.**  `RBM.StepGlue.Eq45Flow` from the three (4.5) inputs
— `RBM.Gauss.eq45Flow_of_inputs` with the auxiliary field `x` unpacked.  Nothing Gaussian is
used: the transfer holds for an arbitrary `X : RBM.Sample B`. -/
theorem eq45Flow_of_eq45FlowInputs (X : Sample B) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hE : |E| ≤ 2 - κ) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    (H : Eq45FlowInputs X E s t) : StepGlue.Eq45Flow X E s t := by
  obtain ⟨x, hIBP, hFArow, hFAblk⟩ := H
  exact Gauss.eq45Flow_of_inputs X hκ0 hκ1 hE hs0 ht1 hIBP hFArow hFAblk

end Slot5

/-! ### The chain with slots 3 and 5 replaced by their producers' inputs -/

section Assembly

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E : ℝ} {s t : ℕ → ℝ}

/-- **The step of the (2.71)-free Theorem 2.21, with slots 3 and 5 replaced.**

Verbatim `RBM.boundsCore_step_of_inputs_reg_W` except that

* `hΘ` is replaced by a `RBM.MomentDuhamelCut.CutHypEv` for `Ξ^{(L-K)}_{·,2}`, and
* `RBM.StepGlue.Eq45Flow` is replaced by `RBM.Eq45FlowInputs`.

`RBM.BoundsCore X E s` is already a hypothesis of this theorem, so the slot-3 producer's
initial condition is free here. -/
theorem boundsCore_step_of_inputs_step345 (X : Sample B) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hEκ : |E| ≤ 2 - κ) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    {c : ℝ} (hc0 : 0 < c) (hreg : Cond272Reg B E s t c) (hB : BoundsCore X E s)
    (h1 : Step1.Hyp X E s t)
    (Hy : ∀ D : ℝ, 60 ≤ D → MomentDuhamelCut.MomentHypCut X E s t D)
    (hcut : MomentDuhamelCut.CutHypEv B.P (fun N u ω => X.xiLK E N u ω 2) s t
      (fun N => Step3.flowAs B E s N ^ ((1 : ℝ) / 2)))
    (h514 : ∀ n, 2 ≤ n → Step3.Lemma514 B.P (Step3.flowXiLK X E s t) (Step3.flowXiL X E s t)
      (Step3.flowA B E s t) n)
    (h45i : Eq45FlowInputs X E s t) (h548 : FlowEq548Sm X E s t) :
    BoundsCore X E t := by
  have hE : |E| < 2 := lt_of_le_of_lt hEκ (by linarith)
  exact boundsCore_step_of_inputs_reg_W X hκ0 hκ1 hEκ hs0 hst ht1 hc0 hreg hB h1 Hy
    (flow_hTheta_of_cutHypEv X hE hs0 hst ht1 hreg.1 hB hcut) h514
    (eq45Flow_of_eq45FlowInputs X hκ0 hκ1 hEκ hs0 ht1 h45i) h548

/-- **The (2.71)-free Theorem 2.21 with slots 3 and 5 of T239's table closed.**

Verbatim `RBM.thm221NoEL_of_inputs_W` except in the third and fifth slots:

* `hΘ` — `Ξ^{(L-K)}_{u,2} ≺ (W ℓ_s η_s)^{1/2}` — is replaced by a
  `RBM.MomentDuhamelCut.CutHypEv` for `Ξ^{(L-K)}_{·,2}` at that threshold, demanded under the
  extra premise `RBM.BoundsCore X E s` (which the step has anyway).  What used to be the
  *conclusion* of Step 3's bootstrap is now *produced* by
  `RBM.flow_hTheta_of_cutHypEv`.
* `RBM.StepGlue.Eq45Flow` is replaced by `RBM.Eq45FlowInputs`, i.e. by the three inputs of
  (4.5) themselves.  `RBM.Gauss.eq45Flow_of_inputs` produces the transfer from them.

Neither `RBM.StochDom B.P (RBM.Step3.flowXiLK X E s t 2) …` nor `RBM.StepGlue.Eq45Flow` occurs
in the hypothesis table any more. -/
theorem thm221NoEL_of_inputs_step345 (X : Sample B) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (h1 : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg B E s t c → Step1.Hyp X E s t)
    (Hy : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg B E s t c →
      ∀ D : ℝ, 60 ≤ D → MomentDuhamelCut.MomentHypCut X E s t D)
    (hcut : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg B E s t c → BoundsCore X E s →
      MomentDuhamelCut.CutHypEv B.P (fun N u ω => X.xiLK E N u ω 2) s t
        (fun N => Step3.flowAs B E s N ^ ((1 : ℝ) / 2)))
    (h514 : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg B E s t c → ∀ n : ℕ, 2 ≤ n →
      Step3.Lemma514 B.P (Step3.flowXiLK X E s t) (Step3.flowXiL X E s t)
        (Step3.flowA B E s t) n)
    (h45i : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg B E s t c → Eq45FlowInputs X E s t)
    (h548 : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg B E s t c → FlowEq548Sm X E s t) :
    Thm221NoEL X κ where
  step E hE c hc0 s t hs0 hst ht1 hreg hB :=
    boundsCore_step_of_inputs_step345 X hκ0 hκ1 hE hs0 hst ht1 hc0 hreg hB
      (h1 E hE s t hs0 hst ht1 c hc0 hreg) (Hy E hE s t hs0 hst ht1 c hc0 hreg)
      (hcut E hE s t hs0 hst ht1 c hc0 hreg hB) (h514 E hE s t hs0 hst ht1 c hc0 hreg)
      (h45i E hE s t hs0 hst ht1 c hc0 hreg) (h548 E hE s t hs0 hst ht1 c hc0 hreg)

/-- **The conclusion did not change.**  The step produced here and
`RBM.boundsCore_step_of_inputs_reg_W`'s step land at the *same* `RBM.BoundsCore X E t`: the
replacement happened strictly in the hypothesis positions, and what went in is a theorem
*producing* the old hypothesis. -/
theorem thm221NoEL_of_inputs_step345_conclusion_unchanged (X : Sample B) {κ : ℝ} (hκ0 : 0 < κ)
    (hκ1 : κ ≤ 1) (hEκ : |E| ≤ 2 - κ) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c) (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore X E s) (h1 : Step1.Hyp X E s t)
    (Hy : ∀ D : ℝ, 60 ≤ D → MomentDuhamelCut.MomentHypCut X E s t D)
    (hcut : MomentDuhamelCut.CutHypEv B.P (fun N u ω => X.xiLK E N u ω 2) s t
      (fun N => Step3.flowAs B E s N ^ ((1 : ℝ) / 2)))
    (h514 : ∀ n, 2 ≤ n → Step3.Lemma514 B.P (Step3.flowXiLK X E s t) (Step3.flowXiL X E s t)
      (Step3.flowA B E s t) n)
    (h45i : Eq45FlowInputs X E s t) (h548 : FlowEq548Sm X E s t) :
    boundsCore_step_of_inputs_step345 X hκ0 hκ1 hEκ hs0 hst ht1 hc0 hreg hB h1 Hy hcut h514
        h45i h548 =
      boundsCore_step_of_inputs_reg_W X hκ0 hκ1 hEκ hs0 hst ht1 hc0 hreg hB h1 Hy
        (flow_hTheta_of_cutHypEv X (lt_of_le_of_lt hEκ (by linarith)) hs0 hst ht1 hreg.1 hB
          hcut)
        h514 (eq45Flow_of_eq45FlowInputs X hκ0 hκ1 hEκ hs0 ht1 h45i) h548 :=
  rfl

end Assembly

/-! ### 5. Satisfiability witnesses -/

section Satisfiability

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E : ℝ} {s t : ℕ → ℝ}

/-- **The slot-3 threshold is not below the critical scale.**  `A_s^{1/2} ≥ 1` eventually, so
the `CutHypEv` asked for in `thm221NoEL_of_inputs_step345` is *not* a request for
`Ξ^{(L-K)}_{u,2} ≪ 1` — which `hinit` (`≺ 1`) could never support and which would make the
slot unsatisfiable. -/
theorem step345_threshold_one_le (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hcond : Cond272 B E s t) :
    ∀ᶠ N : ℕ in atTop, (1 : ℝ) ≤ Step3.flowAs B E s N ^ ((1 : ℝ) / 2) :=
  eventually_one_le_flowAs_rpow_half hE hs0 hst ht1 hcond

/-- **The slot-3 conclusion is consistent with the data the chain carries in.**  Read at the
left endpoint `u = s_N`, `Ξ^{(L-K)}_{u,2} ≺ A_s^{1/2}` follows from `RBM.BoundsCore X E s`
alone (via `≺ 1 ≤ A_s^{1/2}`).  So slot 3 does not ask for anything that already contradicts
slot 6's inputs at `u = s`; the content of the slot is the propagation to `u > s`. -/
theorem step345_theta_left_endpoint (X : Sample B) (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hcond : Cond272 B E s t)
    (hB : BoundsCore X E s) :
    StochDom B.P (fun N (_ : Unit) ω => X.xiLK E N (s N) ω 2)
      (fun N _ _ => Step3.flowAs B E s N ^ ((1 : ℝ) / 2)) := by
  have sc := Step3.scales_flow (E := E) (s := s) (t := t) hE hs0 hst ht1 hcond
  refine Step3.stochDom_mono (fun N _ _ => Real.rpow_nonneg (sc.As_pos N).le _) 1 ?_
    (xiLK_two_init_of_boundsCore X hE hs0 hst ht1 hB)
  filter_upwards [eventually_one_le_flowAs_rpow_half hE hs0 hst ht1 hcond] with N hN _ _
  simpa using hN

/-- The canonical choice of the auxiliary field: `x N u ω i = G_u(ii) - m`, i.e. the diagonal
Green entry itself rather than its conditional expectation `E_i(G_u(ii) - m)`. -/
noncomputable def xCanon (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) :
    ∀ N, TimeIcc s t N → Ω → B.Idx N → ℂ :=
  fun N u ω i => green (X.H N (u : ℝ) ω) (zt E (u : ℝ)) i i - mE E

/-- **`RBM.Gauss.FlucRowFlow` holds at `xCanon`, for every sample and every model**: the
dominated quantity is identically `0`, and the control `L^max_u` is nonnegative. -/
theorem flucRowFlow_canonical (X : Sample B) :
    Gauss.FlucRowFlow X E s t (xCanon X E s t) := by
  refine StochDom.of_eventually_empty fun τ hτ => Eventually.of_forall fun N => ?_
  refine Set.eq_empty_iff_forall_notMem.2 fun ω hω => ?_
  obtain ⟨p, hp⟩ := hω
  simp only [xCanon, sub_self, mul_zero, Finset.sum_const_zero, norm_zero] at hp
  have hL : (0 : ℝ) ≤ Lmax (X.H N p.1 ω) (zt E p.1) := Lmax_nonneg (X.hermitian N p.1 ω)
  have hN : (0 : ℝ) ≤ (N : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg N) _
  nlinarith

/-- **`RBM.Gauss.FlucBlkFlow` holds at `xCanon`**, for the same reason. -/
theorem flucBlkFlow_canonical (X : Sample B) :
    Gauss.FlucBlkFlow X E s t (xCanon X E s t) := by
  refine StochDom.of_eventually_empty fun τ hτ => Eventually.of_forall fun N => ?_
  refine Set.eq_empty_iff_forall_notMem.2 fun ω hω => ?_
  obtain ⟨p, hp⟩ := hω
  simp only [xCanon, sub_self, mul_zero, Finset.sum_const_zero, norm_zero] at hp
  have hL : (0 : ℝ) ≤ Lmax (X.H N p.1 ω) (zt E p.1) := Lmax_nonneg (X.hermitian N p.1 ω)
  have hN : (0 : ℝ) ≤ (N : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg N) _
  nlinarith

/-- **`RBM.Eq45FlowInputs` reduces to a single statement**: two of its three fields are free at
`xCanon`, so the bundle is satisfied as soon as the integration-by-parts display holds there.

⚠ **Not the route to take.**  At `x = G_{ii} - m` the surviving `RBM.Gauss.IBPFlow` reads
`|(G_u(ii) - m) - u m² ∑_k S_{ik}(G_u(kk) - m)| ≺ L^max_u`, i.e. the self-consistent equation
with error `≺ L^max ≍ Ψ²` — the entire content of §4, *not* a weakening of the triple at the
paper's `x = E_i(G_u(ii) - m)`.  This theorem is recorded only as a non-vacuity witness: the
three fields of `RBM.Eq45FlowInputs` are not jointly contradictory. -/
theorem eq45FlowInputs_of_ibpFlow_canonical (X : Sample B)
    (hIBP : Gauss.IBPFlow X E s t (xCanon X E s t)) : Eq45FlowInputs X E s t :=
  ⟨xCanon X E s t, hIBP, flucRowFlow_canonical X, flucBlkFlow_canonical X⟩

/-- **`RBM.Eq45FlowInputs` cannot be satisfied by fiat.**  Whatever the auxiliary field `x` is,
the bundle *implies* (4.5) itself in the form `|L_{u,σ,a} - K_{u,σ,a}| ≺ L^max_u`, uniformly in
`u ∈ [s,t]` — a statement about the model, not about `x`.  So no choice of `x` can make all
three conjuncts simultaneously empty: `x` can trivialize at most two of them
(`flucRowFlow_canonical` / `flucBlkFlow_canonical` do exactly that), and whatever survives
carries the whole of §4. -/
theorem eq45FlowInputs_nonfiat (X : Sample B) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hE : |E| ≤ 2 - κ) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    (H : Eq45FlowInputs X E s t) :
    StochDom B.P
      (fun N (p : TimeIcc s t N × LoopData (B.L N) 1) ω => X.lkErr E N p.1 ω p.2.idx)
      (fun N p ω => Lmax (X.H N p.1 ω) (zt E p.1)) := by
  obtain ⟨x, hIBP, hFArow, hFAblk⟩ := H
  exact Gauss.stochDom_lkErr_one_Lmax X hκ0 hκ1 hE hs0 ht1 hIBP hFArow hFAblk

end Satisfiability

/-! ### 6. The merged assembly (T245): four of T239's six slots closed at once

T239's main-chain hypothesis table had six slots.  Four of them were closed in four separate
places, and **no single assembly had all four closed at once** — this section is that assembly.

| T239 slot | how it leaves the table | where |
|---|---|---|
| 1 `RBM.Step1.Hyp` | producer `RBM.Gauss.step1Hyp_slot` (Gaussian model) | T242 |
| 3 `hΘ` | replaced by `RBM.MomentDuhamelCut.CutHypEv` + `RBM.flow_hTheta_of_cutHypEv` | T243, §1 |
| 5 `RBM.StepGlue.Eq45Flow` | `RBM.Eq45FlowInputs` + `eq45Flow_of_eq45FlowInputs` | T243, §2 |
| 6 `RBM.Eq548EntryData.init` | producer `RBM.stochDom_jSfarSm_init_of_boundsCore` | T241 |

and two more items inside slot 6 go with them: `meas`, which T244 proved with **no**
hypotheses (`RBM.aestronglyMeasurable_jSfarSm`), and `modulus`, which T244 proved **false** in
its `∀ N` shape and which is now read at `∀ᶠ N in atTop` (`RBM.EntryModulusEv`).

**Direction of each replacement, for the audit.**  Three of the six changes are *free*: they
delete a field (`init`, `meas`) or weaken one (`modulus` to its `∀ᶠ N` reading), so
`RBM.thm221NoEL_of_inputs_entriesEv_of_unprimed` compiles — anything satisfying T239's table
satisfies that one.  Slot 1 is free as well: `RBM.Gauss.step1Hyp_slot` adds no hypothesis.
Slots 3 and 5 are **not** free and must not be claimed as such: `RBM.CutHypEv` *implies* `hΘ`
(`RBM.flow_hTheta_of_cutHypEv`) and `RBM.Eq45FlowInputs` *implies* `RBM.StepGlue.Eq45Flow`
(`RBM.eq45Flow_of_eq45FlowInputs`), so those two slots are genuinely *different, stronger*
requests, justified by having producers rather than by being weaker.  Both implications are
compiled, and `RBM.thm221NoEL_of_inputs_merged_slots_imply_old` states the three of them in one
place.

What remains in the merged table, both here and in the Gaussian version: slot 2
`RBM.MomentDuhamelCut.MomentHypCut` (→ T230 `(A′)`), slot 4 `RBM.Step3.Lemma514` (→ T236), the
`CutHypEv` of slot 3 (its `moment` field → T230), slot 5's `RBM.Eq45FlowInputs` (→ T124's
follow-up), and slot 6's `near` (→ T207/`Step2Near47`) and `moment` (→ T230/T210). -/

section Merged

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E : ℝ} {s t : ℕ → ℝ}

/-- **The step of the (2.71)-free Theorem 2.21, with slots 3, 5 and the three closed items of
slot 6 replaced.**  Verbatim `RBM.boundsCore_step_of_inputs_step345` except in the last slot,
where `RBM.FlowEq548Sm` is replaced by `RBM.Eq548EntryDataEv`. -/
theorem boundsCore_step_of_inputs_merged (X : Sample B) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hEκ : |E| ≤ 2 - κ) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    {c : ℝ} (hc0 : 0 < c) (hreg : Cond272Reg B E s t c) (hB : BoundsCore X E s)
    (h1 : Step1.Hyp X E s t)
    (Hy : ∀ D : ℝ, 60 ≤ D → MomentDuhamelCut.MomentHypCut X E s t D)
    (hcut : MomentDuhamelCut.CutHypEv B.P (fun N u ω => X.xiLK E N u ω 2) s t
      (fun N => Step3.flowAs B E s N ^ ((1 : ℝ) / 2)))
    (h514 : ∀ n, 2 ≤ n → Step3.Lemma514 B.P (Step3.flowXiLK X E s t) (Step3.flowXiL X E s t)
      (Step3.flowA B E s t) n)
    (h45i : Eq45FlowInputs X E s t) (H : Eq548EntryDataEv X E s t) :
    BoundsCore X E t :=
  boundsCore_step_of_inputs_step345 X hκ0 hκ1 hEκ hs0 hst ht1 hc0 hreg hB h1 Hy hcut h514 h45i
    (flowEq548Sm_of_entryDataEv X (lt_of_le_of_lt hEκ (by linarith)) hs0 hst ht1
      hreg.toCond272 hB H)

/-- **The conclusion is byte-identical to `RBM.boundsCore_step_of_inputs_reg_W`'s.**  Every
substitution happened in a hypothesis position; what went in each time is a theorem
*producing* the old hypothesis. -/
theorem boundsCore_step_of_inputs_merged_unchanged (X : Sample B) {κ : ℝ} (hκ0 : 0 < κ)
    (hκ1 : κ ≤ 1) (hEκ : |E| ≤ 2 - κ) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c) (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore X E s) (h1 : Step1.Hyp X E s t)
    (Hy : ∀ D : ℝ, 60 ≤ D → MomentDuhamelCut.MomentHypCut X E s t D)
    (hcut : MomentDuhamelCut.CutHypEv B.P (fun N u ω => X.xiLK E N u ω 2) s t
      (fun N => Step3.flowAs B E s N ^ ((1 : ℝ) / 2)))
    (h514 : ∀ n, 2 ≤ n → Step3.Lemma514 B.P (Step3.flowXiLK X E s t) (Step3.flowXiL X E s t)
      (Step3.flowA B E s t) n)
    (h45i : Eq45FlowInputs X E s t) (H : Eq548EntryDataEv X E s t) :
    boundsCore_step_of_inputs_merged X hκ0 hκ1 hEκ hs0 hst ht1 hc0 hreg hB h1 Hy hcut h514
        h45i H =
      boundsCore_step_of_inputs_reg_W X hκ0 hκ1 hEκ hs0 hst ht1 hc0 hreg hB h1 Hy
        (flow_hTheta_of_cutHypEv X (lt_of_le_of_lt hEκ (by linarith)) hs0 hst ht1 hreg.1 hB
          hcut)
        h514 (eq45Flow_of_eq45FlowInputs X hκ0 hκ1 hEκ hs0 ht1 h45i)
        (flowEq548Sm_of_entryDataEv X (lt_of_le_of_lt hEκ (by linarith)) hs0 hst ht1
          hreg.toCond272 hB H) :=
  rfl

/-- **The merged assembly, general band** (T245): T239's slots 3, 5 and the `init`/`meas`/`∀ N`
modulus of slot 6 are all gone at once.

The table is
`RBM.Step1.Hyp` · `RBM.MomentDuhamelCut.MomentHypCut` · **`RBM.MomentDuhamelCut.CutHypEv`** ·
`RBM.Step3.Lemma514` · **`RBM.Eq45FlowInputs`** · **`RBM.Eq548EntryDataEv`**, and the
conclusion is `RBM.Thm221NoEL X κ`, byte for byte the conclusion of
`RBM.thm221NoEL_of_inputs_W`.

`RBM.Step1.Hyp` survives here because its producer is Gaussian;
`RBM.Gauss.thm221NoEL_of_inputs_merged_gauss` removes it. -/
theorem thm221NoEL_of_inputs_merged (X : Sample B) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (h1 : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg B E s t c → Step1.Hyp X E s t)
    (Hy : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg B E s t c →
      ∀ D : ℝ, 60 ≤ D → MomentDuhamelCut.MomentHypCut X E s t D)
    (hcut : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg B E s t c → BoundsCore X E s →
      MomentDuhamelCut.CutHypEv B.P (fun N u ω => X.xiLK E N u ω 2) s t
        (fun N => Step3.flowAs B E s N ^ ((1 : ℝ) / 2)))
    (h514 : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg B E s t c → ∀ n : ℕ, 2 ≤ n →
      Step3.Lemma514 B.P (Step3.flowXiLK X E s t) (Step3.flowXiL X E s t)
        (Step3.flowA B E s t) n)
    (h45i : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg B E s t c → Eq45FlowInputs X E s t)
    (h548e : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg B E s t c → Eq548EntryDataEv X E s t) :
    Thm221NoEL X κ where
  step E hE c hc0 s t hs0 hst ht1 hreg hB :=
    boundsCore_step_of_inputs_merged X hκ0 hκ1 hE hs0 hst ht1 hc0 hreg hB
      (h1 E hE s t hs0 hst ht1 c hc0 hreg) (Hy E hE s t hs0 hst ht1 c hc0 hreg)
      (hcut E hE s t hs0 hst ht1 c hc0 hreg hB) (h514 E hE s t hs0 hst ht1 c hc0 hreg)
      (h45i E hE s t hs0 hst ht1 c hc0 hreg) (h548e E hE s t hs0 hst ht1 c hc0 hreg)

/-- **The three slot-wise implications, in one statement** — the audit of the *direction* of
each replacement.  Slot 6 goes the free way (old package ⟹ new), slots 3 and 5 the other way
(new request ⟹ old hypothesis, which is what licenses the substitution). -/
theorem thm221NoEL_of_inputs_merged_slots_imply_old (X : Sample B) {κ : ℝ} (hκ0 : 0 < κ)
    (hκ1 : κ ≤ 1) (hEκ : |E| ≤ 2 - κ) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) {c : ℝ} (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore X E s) :
    (MomentDuhamelCut.CutHypEv B.P (fun N u ω => X.xiLK E N u ω 2) s t
        (fun N => Step3.flowAs B E s N ^ ((1 : ℝ) / 2)) →
      StochDom B.P (Step3.flowXiLK X E s t 2)
        (fun N (_ : TimeIcc s t N) (_ : Ω) => Step3.flowAs B E s N ^ ((1 : ℝ) / 2))) ∧
    (Eq45FlowInputs X E s t → StepGlue.Eq45Flow X E s t) ∧
    (Eq548EntryData X E s t → Eq548EntryDataEv X E s t) :=
  ⟨flow_hTheta_of_cutHypEv X (lt_of_le_of_lt hEκ (by linarith)) hs0 hst ht1 hreg.1 hB,
    eq45Flow_of_eq45FlowInputs X hκ0 hκ1 hEκ hs0 ht1,
    fun H => H.toEv⟩

end Merged

namespace Gauss

/-! ### 7. The merged assembly on the Gaussian model: slot 1 gone too (T245) -/

section MergedGauss

variable {d : Dims}

/-- **The merged assembly, Gaussian model** (T245): T239's table minus slots 1, 3, 5 and minus
`init`/`meas`/the refuted `∀ N` modulus of slot 6 — **four of the six slots closed in one
theorem**, with `RBM.Thm221NoEL (Gauss.sample d) κ` as the conclusion.

Everything left in the table:

* `Hy` — slot 2, `RBM.MomentDuhamelCut.MomentHypCut` at every `D ≥ 60` (→ T230 `(A′)`);
* `hcut` — slot 3's residue, a `RBM.MomentDuhamelCut.CutHypEv` for `Ξ^{(L-K)}_{·,2}` at the
  threshold `A_s^{1/2}`, asked under the free extra premise `RBM.BoundsCore` (→ T230 for its
  `moment` field);
* `h514` — slot 4, Lemma 5.14 at every `n ≥ 2` (→ T236);
* `h45i` — slot 5's residue, `RBM.Eq45FlowInputs` (→ T124's follow-up);
* `h548e` — slot 6's residue, `RBM.Eq548EntryDataEv`: `near` (→ T207) and `moment` (→ T230),
  plus `modulus` at T244's repaired `∀ᶠ N` shape. -/
theorem thm221NoEL_of_inputs_merged_gauss (d : Dims) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (Hy : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg (band d) E s t c →
      ∀ D : ℝ, 60 ≤ D → MomentDuhamelCut.MomentHypCut (sample d) E s t D)
    (hcut : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg (band d) E s t c →
      BoundsCore (sample d) E s →
      MomentDuhamelCut.CutHypEv (band d).P (fun N u ω => (sample d).xiLK E N u ω 2) s t
        (fun N => Step3.flowAs (band d) E s N ^ ((1 : ℝ) / 2)))
    (h514 : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg (band d) E s t c → ∀ n : ℕ, 2 ≤ n →
      Step3.Lemma514 (band d).P (Step3.flowXiLK (sample d) E s t)
        (Step3.flowXiL (sample d) E s t) (Step3.flowA (band d) E s t) n)
    (h45i : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg (band d) E s t c →
      Eq45FlowInputs (sample d) E s t)
    (h548e : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg (band d) E s t c →
      Eq548EntryDataEv (sample d) E s t) :
    Thm221NoEL (sample d) κ where
  step E hE c hc0 s t hs0 hst ht1 hreg hB :=
    boundsCore_step_of_inputs_merged (sample d) hκ0 hκ1 hE hs0 hst ht1 hc0 hreg hB
      (step1Hyp_slot d hκ0 E hE s t hs0 hst ht1 c hc0 hreg hB)
      (Hy E hE s t hs0 hst ht1 c hc0 hreg) (hcut E hE s t hs0 hst ht1 c hc0 hreg hB)
      (h514 E hE s t hs0 hst ht1 c hc0 hreg) (h45i E hE s t hs0 hst ht1 c hc0 hreg)
      (h548e E hE s t hs0 hst ht1 c hc0 hreg)

/-- **The Gaussian merged table is weaker than T242's** — the four inputs of
`RBM.Gauss.thm221NoEL_of_inputs_entries_gauss` that are *not* slots 3 and 5 are enough, the
slot-6 package via `RBM.Eq548EntryData.toEv`.  So the three free changes (slot 6's `init`,
`meas` and the `∀ N` modulus) really are free; slots 3 and 5 are supplied here from their own
producers' inputs, which is the direction `RBM.thm221NoEL_of_inputs_merged_slots_imply_old`
records. -/
theorem thm221NoEL_of_inputs_merged_gauss_of_unprimed (d : Dims) {κ : ℝ} (hκ0 : 0 < κ)
    (hκ1 : κ ≤ 1)
    (Hy : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg (band d) E s t c →
      ∀ D : ℝ, 60 ≤ D → MomentDuhamelCut.MomentHypCut (sample d) E s t D)
    (hcut : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg (band d) E s t c →
      BoundsCore (sample d) E s →
      MomentDuhamelCut.CutHypEv (band d).P (fun N u ω => (sample d).xiLK E N u ω 2) s t
        (fun N => Step3.flowAs (band d) E s N ^ ((1 : ℝ) / 2)))
    (h514 : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg (band d) E s t c → ∀ n : ℕ, 2 ≤ n →
      Step3.Lemma514 (band d).P (Step3.flowXiLK (sample d) E s t)
        (Step3.flowXiL (sample d) E s t) (Step3.flowA (band d) E s t) n)
    (h45i : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg (band d) E s t c →
      Eq45FlowInputs (sample d) E s t)
    (h548e : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg (band d) E s t c →
      Eq548EntryData (sample d) E s t) :
    Thm221NoEL (sample d) κ :=
  thm221NoEL_of_inputs_merged_gauss d hκ0 hκ1 Hy hcut h514 h45i
    fun E hE s t hs0 hst ht1 c hc0 hreg => (h548e E hE s t hs0 hst ht1 c hc0 hreg).toEv

end MergedGauss

/-! ### 8. Joint satisfiability of the three producers the merged assembly invokes (T245) -/

section MergedWitness

open Filter

/-- **The three producers the merged assembly calls all fire, simultaneously, on T202's
explicit model.**

At `E = 0` on `RBM.Gauss.band RBM.Gauss.Dims.exampleGrow` and the first step
`s ≡ 0 → t = u_1` of the grid of p. 24 — the very step `RBM.thm221Assembly_hyp_consistent`
certifies — the hypotheses of

* `RBM.Gauss.step1Hyp_slot` (slot 1's producer),
* `RBM.eventually_one_le_flowAs_rpow_half` (slot 3's threshold `A_s^{1/2} ≥ 1`, so the
  `CutHypEv` asked for is not the unsatisfiable request `Ξ^{(L-K)}_{u,2} ≪ 1`), and
* `RBM.stochDom_jSfarSm_init_of_boundsCore` (slot 6's deleted `init`)

hold at once, and each producer *returns its conclusion* there.  The window does not collapse
(`0 = u_0 < u_1`, `RBM.Gauss.eventually_gridT_zero_lt_gridT_one`), the scale does not collapse
(`RBM.Cond272Reg`'s second component gives `N^c ≤ W ℓ η` with `c > 0`, chosen **before** `E`
and `t`), and `RBM.thm221Assembly_far_critical` says the `init` conclusion is a *critical*
request — `1 ≤ J*^{sm}` at **every** `ω`, including `ω = 0`. -/
theorem thm221Merged_witness {τ : ℝ} (hτ0 : 0 < τ) :
    ∃ τ' : ℝ, 0 < τ' ∧ ∃ c : ℝ, 0 < c ∧
      ∀ t : ℕ → ℝ, (∀ N, 0 ≤ t N) →
        (∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-1 + τ) ≤ 1 - t N) →
        ∃ v : ℕ → ℝ, (∀ N, (0 : ℝ) ≤ v N) ∧ (∀ N, v N < 1) ∧
          Cond272Reg (band Dims.exampleGrow) 0 (fun _ => 0) v c ∧
          BoundsCore (sample Dims.exampleGrow) 0 (fun _ => 0) ∧
          Step1.Hyp (sample Dims.exampleGrow) 0 (fun _ => 0) v ∧
          (∀ᶠ N : ℕ in atTop,
            (1 : ℝ) ≤ Step3.flowAs (band Dims.exampleGrow) 0 (fun _ => 0) N ^
              ((1 : ℝ) / 2)) ∧
          ∀ D : ℝ, 0 < D → StochDom (band Dims.exampleGrow).P
            (fun N (_ : Unit) ω =>
              Step2FarMart.jSfarSm (sample Dims.exampleGrow) 0 D N 0 ω)
            (fun _ _ _ => (1 : ℝ)) := by
  obtain ⟨τ', hτ'0, c, hc0, hwit⟩ := thm221Assembly_init_witness (τ := τ) hτ0
  refine ⟨τ', hτ'0, c, hc0, fun t ht0 ht => ?_⟩
  obtain ⟨v, hv0, hv1, hreg, hB, hinit⟩ := hwit t ht0 ht
  refine ⟨v, hv0, hv1, hreg, hB, ?_, ?_, hinit⟩
  · exact step1Hyp_slot Dims.exampleGrow (κ := 1) one_pos 0 (by norm_num)
      (fun _ => 0) v (fun _ => le_rfl) hv0 hv1 c hc0 hreg hB
  · exact eventually_one_le_flowAs_rpow_half (B := band Dims.exampleGrow) (t := v)
      (by norm_num) (fun _ => le_rfl) hv0 hv1 hreg.toCond272

end MergedWitness

end Gauss

/-! ### 9. T251: the window's left endpoint, and the merged table on an event

T249 proved two things about the `modulus` field of `RBM.MomentDuhamelCut.CutHypEv` and of
`RBM.Eq548EntryDataEv`, both by compiling a refutation:

1. it is **false** when the window starts at `0` (`RBM.not_entryModulusEv_swapSample_of_far`),
   because `J*^{sm}_{0,D} ≡ 1` for *every* `ω` (`RBM.jSfarSm_zero`, i.e. (2.67)) while the
   same functional is genuinely moving at every `v > 0`;
2. restricting `ω` to `{‖X‖ ≤ N}` does **not** repair 1., since that event still contains
   `X = v^{-1/2} A` as soon as `v ≥ N^{-2}`.

So the two repairs have to be made together: the event restriction (§9 of
`Flow/Thm221Assembly.lean`, `RBM.Eq548EntryDataEvOn'`) **and** a left endpoint bounded below,
`RBM.WindowLeft s C`, i.e. `N^{-C} ≤ s_N` eventually.  With `s_N ≥ N^{-C}` the Lipschitz
constant T249乙 computes for `u ↦ G_u` along `H_u = √u X` on `{‖X‖ ≤ N}` is
`≤ N^{C} · C(E, t₀)`, i.e. finite and polynomial, which is exactly what `Kmod` asks for.

**Which grid cells survive.**  The induction of p. 24 runs on `u_k = min(1 - W^{-kτ'}, t)`.
`RBM.windowLeft_gridT_succ` shows **every** cell `k ↦ k+1` with `k ≥ 1` satisfies
`RBM.WindowLeft` (as soon as `t` is eventually bounded below by a positive constant), and
`RBM.not_windowLeft_zero` shows the cell `k = 0` **never** does — `u_0 ≡ 0`
(`RBM.gridT_zero`), and `N^{-C} > 0`.  So the answer to the ticket's question is:
*the `s ≡ 0` cell is genuinely needed by the induction and this chain cannot supply it.*
`RBM.Thm221NoELFrom` is Theorem 2.21 with that cell removed from its `step`, and
`RBM.thm221NoEL_of_from` is the exact statement of what is still owed — the single step
`u_0 = 0 → u_1`, which has to come from somewhere other than (5.48)'s far martingale.

**Directions, for the audit.**  Every change here is a *weakening* of the table:
`RBM.Thm221NoEL.toFrom` (the conclusion is weaker),
`RBM.MomentDuhamelCut.CutHypEvOn.of_cutHypEv` and `RBM.Eq548EntryDataEv.toEvOn'` (the slots are
weaker), and `RBM.thm221NoEL_of_inputs_merged_gauss'_of_unprimed` is the one compiled
certificate that T245's table implies this one. -/

section WindowLeft

open Filter

/-- **The window's left endpoint is not `0`**: `N^{-C} ≤ s_N` for all large `N`.

This is the *time*-side half of T249's repair; `RBM.Eq548EntryDataEvOn'` is the `ω`-side half.
Neither works alone (T249, `⚠`). -/
def WindowLeft (s : ℕ → ℝ) (C : ℝ) : Prop := ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-C) ≤ s N

/-- **The degenerate window `s ≡ 0` never satisfies it** — for *any* `C`, not only `C > 0`.
This is the compiled form of the answer to T251's question: the first cell of the grid of
p. 24 is *excluded* by the new premise, not merely awkward. -/
theorem not_windowLeft_zero (C : ℝ) : ¬ WindowLeft (fun _ => (0 : ℝ)) C := by
  intro h
  obtain ⟨N, hN⟩ := (h.and (eventually_ge_atTop 1)).exists
  have h1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN.2
  have : (0 : ℝ) < (N : ℝ) ^ (-C) := Real.rpow_pos_of_pos (by linarith) _
  linarith [hN.1]

/-- **Every later cell of the grid of p. 24 does satisfy it.**  `u_{k+1} = min(1 - W^{-(k+1)τ'},
t_N)`; the first entry is `≥ 1 - W^{-τ'} → 1` by (2.2) (`RBM.Step2.tendsto_W`) and the second
is `≥ t₀ > 0` by hypothesis, while `N^{-C} → 0`.

So the only obstruction the new premise creates is at `k = 0`. -/
theorem windowLeft_gridT_succ {Ωb : Type*} [MeasurableSpace Ωb] (B : Band Ωb) {τ' : ℝ}
    (hτ' : 0 < τ') {t : ℕ → ℝ} {t₀ : ℝ} (ht₀ : 0 < t₀) (ht : ∀ᶠ N : ℕ in atTop, t₀ ≤ t N)
    {C : ℝ} (hC : 0 < C) (k : ℕ) :
    WindowLeft (fun N => gridT ((B.W N : ℝ)) τ' (t N) (k + 1)) C := by
  have hWt : Tendsto (fun N : ℕ => ((B.W N : ℝ)) ^ (-τ')) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hτ').comp (Step2.tendsto_W B)
  have hNt : Tendsto (fun N : ℕ => ((N : ℝ)) ^ (-C)) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hC).comp tendsto_natCast_atTop_atTop
  have hW2 : ∀ᶠ N : ℕ in atTop, ((B.W N : ℝ)) ^ (-τ') < 1 / 2 :=
    hWt.eventually_lt_const (by norm_num)
  have hN2 : ∀ᶠ N : ℕ in atTop, ((N : ℝ)) ^ (-C) < min t₀ (1 / 2) :=
    hNt.eventually_lt_const (by positivity)
  filter_upwards [ht, hW2, hN2, (Step2.tendsto_W B).eventually_ge_atTop 2] with
    N htN hWN hNN hW2N
  have hW1 : (1 : ℝ) ≤ (B.W N : ℝ) := by linarith
  have hmono : gridS ((B.W N : ℝ)) τ' 1 ≤ gridS ((B.W N : ℝ)) τ' (k + 1) :=
    gridS_mono hW1 hτ'.le (Nat.succ_le_succ (Nat.zero_le k))
  have hg1 : gridS ((B.W N : ℝ)) τ' 1 = 1 - ((B.W N : ℝ)) ^ (-τ') := by
    rw [gridS]; norm_num
  rw [gridT]
  refine le_min ?_ ?_
  · have : (1 : ℝ) / 2 ≤ gridS ((B.W N : ℝ)) τ' 1 := by rw [hg1]; linarith
    have h2 := lt_of_lt_of_le hNN (min_le_right t₀ (1 / 2))
    linarith
  · have h2 := lt_of_lt_of_le hNN (min_le_left t₀ (1 / 2))
    linarith


/-- **The first cell of p. 24's grid is the one that is excluded.**  `u_0 = 0`
(`RBM.gridT_zero`), so `RBM.not_windowLeft_zero` applies to it verbatim.  With
`RBM.windowLeft_gridT_succ` this is the complete answer to T251's question: on the induction
of p. 24 the repaired (5.48) chain covers the cells `k ↦ k+1` for `k ≥ 1` and **only** those. -/
theorem not_windowLeft_gridT_zero {Ωb : Type*} [MeasurableSpace Ωb] (B : Band Ωb) {τ' : ℝ}
    {t : ℕ → ℝ} (ht0 : ∀ N, 0 ≤ t N) (C : ℝ) :
    ¬ WindowLeft (fun N => gridT ((B.W N : ℝ)) τ' (t N) 0) C := by
  have : (fun N => gridT ((B.W N : ℝ)) τ' (t N) 0) = fun _ : ℕ => (0 : ℝ) :=
    funext fun N => gridT_zero (ht0 N)
  rw [this]
  exact not_windowLeft_zero C

end WindowLeft

section Slot3On

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E : ℝ} {s t : ℕ → ℝ}

/-- **Slot 3's input, with the deterministic modulus on an event** — the event, its
measurability and its high probability are quantified inside, so the slot is a `Prop` about
`X, E, s, t` alone. -/
def CutHypEvOnSlot (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) : Prop :=
  ∃ Good : ℕ → Set Ω, (∀ N, MeasurableSet (Good N)) ∧ HighProb B.P Good ∧
    Nonempty (MomentDuhamelCut.CutHypEvOn B.P (fun N u ω => X.xiLK E N u ω 2) s t
      (fun N => Step3.flowAs B E s N ^ ((1 : ℝ) / 2)) Good)

/-- The unrestricted slot-3 input is the `Good = Set.univ` case, so the new slot is weaker. -/
theorem cutHypEvOnSlot_of_cutHypEv {X : Sample B}
    (H : MomentDuhamelCut.CutHypEv B.P (fun N u ω => X.xiLK E N u ω 2) s t
      (fun N => Step3.flowAs B E s N ^ ((1 : ℝ) / 2))) :
    CutHypEvOnSlot X E s t :=
  ⟨fun _ => Set.univ, fun _ => MeasurableSet.univ, highProb_univ B.P,
    ⟨MomentDuhamelCut.CutHypEvOn.of_cutHypEv H⟩⟩

/-- **`RBM.flow_hTheta_of_cutHypEv` on an event** — `RBM.MomentDuhamelCut.stochDom_of_cutHypEvOn`
in place of `RBM.MomentDuhamelCut.stochDom_of_cutHypEv`; the two side conditions are the same
theorems as there.  The conclusion is **unchanged**: a `StochDom` for the honest, unrestricted
`Ξ^{(L-K)}_{u,2}`. -/
theorem flow_hTheta_of_cutHypEvOn (X : Sample B) (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hcond : Cond272 B E s t)
    (hB : BoundsCore X E s) (H : CutHypEvOnSlot X E s t) :
    StochDom B.P (Step3.flowXiLK X E s t 2)
      (fun N (_ : TimeIcc s t N) (_ : Ω) => Step3.flowAs B E s N ^ ((1 : ℝ) / 2)) := by
  obtain ⟨Good, -, hgood, ⟨H⟩⟩ := H
  have := B.isProbabilityMeasure
  exact MomentDuhamelCut.stochDom_of_cutHypEvOn H hgood
    (eventually_one_le_flowAs_rpow_half hE hs0 hst ht1 hcond)
    (xiLK_two_init_of_boundsCore X hE hs0 hst ht1 hB)

end Slot3On

section MergedOn

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E : ℝ} {s t : ℕ → ℝ}

/-- **Theorem 2.21 without (2.71), with the degenerate window `s ≡ 0` removed from `step`.**

Verbatim `RBM.Thm221NoEL` except for the extra premise `RBM.WindowLeft s C` on the step.  This
is *weaker* than `RBM.Thm221NoEL` (`RBM.Thm221NoEL.toFrom`), and `RBM.not_windowLeft_zero`
says the weakening is real: the cell `u_0 = 0 → u_1` of the grid of p. 24 is exactly what it
gives up. -/
structure Thm221NoELFrom (X : Sample B) (κ C : ℝ) : Prop where
  step : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ c : ℝ, 0 < c → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) →
    (∀ N, s N ≤ t N) → (∀ N, t N < 1) → WindowLeft s C → Cond272Reg B E s t c →
    BoundsCore X E s → BoundsCore X E t

/-- Dropping a cell is a weakening. -/
theorem Thm221NoEL.toFrom {X : Sample B} {κ : ℝ} (h : Thm221NoEL X κ) (C : ℝ) :
    Thm221NoELFrom X κ C where
  step E hE c hc0 s t hs0 hst ht1 _ hreg hB := h.step E hE c hc0 s t hs0 hst ht1 hreg hB

/-- **What is still owed**, stated exactly.  `RBM.Thm221NoELFrom X κ C` plus the steps whose
left endpoint is *not* eventually `≥ N^{-C}` — in the induction of p. 24 that is the single
cell `u_0 = 0 → u_1` — is `RBM.Thm221NoEL X κ`, byte for byte.

The second argument is the honest statement of the gap T249 opened: the far-martingale chain
of (5.48) cannot produce it, because `J*^{sm}_{0,D} ≡ 1` for every `ω` and the chain's
`modulus` is therefore false there. -/
theorem thm221NoEL_of_from {X : Sample B} {κ C : ℝ} (hT : Thm221NoELFrom X κ C)
    (hstart : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ c : ℝ, 0 < c → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) →
      (∀ N, s N ≤ t N) → (∀ N, t N < 1) → ¬ WindowLeft s C → Cond272Reg B E s t c →
      BoundsCore X E s → BoundsCore X E t) :
    Thm221NoEL X κ where
  step E hE c hc0 s t hs0 hst ht1 hreg hB := by
    by_cases hw : WindowLeft s C
    · exact hT.step E hE c hc0 s t hs0 hst ht1 hw hreg hB
    · exact hstart E hE c hc0 s t hs0 hst ht1 hw hreg hB

/-- **The step of the merged assembly, with both halves of T249's repair.**  Verbatim
`RBM.boundsCore_step_of_inputs_merged` except that slots 3 and 6 are the event-restricted
`RBM.CutHypEvOnSlot` and `RBM.Eq548EntryDataEvOn'`.  The `RBM.WindowLeft` premise is *not*
used in this proof — it is carried by the slots themselves in the assembly below; here the
conclusion is already `RBM.BoundsCore X E t`, byte for byte. -/
theorem boundsCore_step_of_inputs_mergedOn (X : Sample B) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hEκ : |E| ≤ 2 - κ) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    {c : ℝ} (hc0 : 0 < c) (hreg : Cond272Reg B E s t c) (hB : BoundsCore X E s)
    (h1 : Step1.Hyp X E s t)
    (Hy : ∀ D : ℝ, 60 ≤ D → MomentDuhamelCut.MomentHypCut X E s t D)
    (hcut : CutHypEvOnSlot X E s t)
    (h514 : ∀ n, 2 ≤ n → Step3.Lemma514 B.P (Step3.flowXiLK X E s t) (Step3.flowXiL X E s t)
      (Step3.flowA B E s t) n)
    (h45i : Eq45FlowInputs X E s t) (H : Eq548EntryDataEvOn' X E s t) :
    BoundsCore X E t :=
  boundsCore_step_of_inputs_reg_W X hκ0 hκ1 hEκ hs0 hst ht1 hc0 hreg hB h1 Hy
    (flow_hTheta_of_cutHypEvOn X (lt_of_le_of_lt hEκ (by linarith)) hs0 hst ht1 hreg.1 hB hcut)
    h514 (eq45Flow_of_eq45FlowInputs X hκ0 hκ1 hEκ hs0 ht1 h45i)
    (flowEq548Sm_of_entryDataEvOn X (lt_of_le_of_lt hEκ (by linarith)) hs0 hst ht1
      hreg.toCond272 hB H)

/-- **The merged assembly with T249's repair, general band.**  The table is

`RBM.Step1.Hyp` · `RBM.MomentDuhamelCut.MomentHypCut` · **`RBM.CutHypEvOnSlot`** ·
`RBM.Step3.Lemma514` · `RBM.Eq45FlowInputs` · **`RBM.Eq548EntryDataEvOn'`**,

the two starred slots asked only on windows with `RBM.WindowLeft s C`, and the conclusion is
`RBM.Thm221NoELFrom X κ C`. -/
theorem thm221NoEL_of_inputs_mergedOn (X : Sample B) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (C : ℝ)
    (h1 : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg B E s t c → Step1.Hyp X E s t)
    (Hy : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg B E s t c →
      ∀ D : ℝ, 60 ≤ D → MomentDuhamelCut.MomentHypCut X E s t D)
    (hcut : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → WindowLeft s C → ∀ c : ℝ, 0 < c → Cond272Reg B E s t c →
      BoundsCore X E s → CutHypEvOnSlot X E s t)
    (h514 : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg B E s t c → ∀ n : ℕ, 2 ≤ n →
      Step3.Lemma514 B.P (Step3.flowXiLK X E s t) (Step3.flowXiL X E s t)
        (Step3.flowA B E s t) n)
    (h45i : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg B E s t c → Eq45FlowInputs X E s t)
    (h548e : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → WindowLeft s C → ∀ c : ℝ, 0 < c → Cond272Reg B E s t c →
      Eq548EntryDataEvOn' X E s t) :
    Thm221NoELFrom X κ C where
  step E hE c hc0 s t hs0 hst ht1 hw hreg hB :=
    boundsCore_step_of_inputs_mergedOn X hκ0 hκ1 hE hs0 hst ht1 hc0 hreg hB
      (h1 E hE s t hs0 hst ht1 c hc0 hreg) (Hy E hE s t hs0 hst ht1 c hc0 hreg)
      (hcut E hE s t hs0 hst ht1 hw c hc0 hreg hB) (h514 E hE s t hs0 hst ht1 c hc0 hreg)
      (h45i E hE s t hs0 hst ht1 c hc0 hreg) (h548e E hE s t hs0 hst ht1 hw c hc0 hreg)

/-- The same, stated as a slot-wise implication: each starred slot of §10's table is implied
by the corresponding slot of T245's. -/
theorem mergedOn_slots_weaker (X : Sample B) :
    (MomentDuhamelCut.CutHypEv B.P (fun N u ω => X.xiLK E N u ω 2) s t
        (fun N => Step3.flowAs B E s N ^ ((1 : ℝ) / 2)) → CutHypEvOnSlot X E s t) ∧
      (Eq548EntryDataEv X E s t → Eq548EntryDataEvOn' X E s t) :=
  ⟨cutHypEvOnSlot_of_cutHypEv, fun H => H.toEvOn'⟩

end MergedOn

namespace Gauss

/-! ### 10. T251: the merged assembly on the Gaussian model, with T249's repair -/

section MergedOnGauss

variable {d : Dims}

/-- **The merged assembly with T249's repair, Gaussian model** — `RBM.Step1.Hyp` gone as in
`RBM.Gauss.thm221NoEL_of_inputs_merged_gauss`, slots 3 and 6 event-restricted and asked only
on windows with `RBM.WindowLeft s C`.

Everything left in the table:

* `Hy` — slot 2, `RBM.MomentDuhamelCut.MomentHypCut` at every `D ≥ 60` (→ T230 `(A′)`);
* `hcut` — slot 3's residue, now `RBM.CutHypEvOnSlot` (→ T230 for its `moment` field);
* `h514` — slot 4, Lemma 5.14 at every `n ≥ 2` (→ T236);
* `h45i` — slot 5's residue, `RBM.Eq45FlowInputs` (→ T124's follow-up);
* `h548e` — slot 6's residue, `RBM.Eq548EntryDataEvOn'`: `near` (→ T207), `moment` (→ T230),
  and `modulus` at T244's `∀ᶠ N` shape restricted to a high-probability event (T249丙). -/
theorem thm221NoEL_of_inputs_mergedOn_gauss (d : Dims) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (C : ℝ)
    (Hy : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg (band d) E s t c →
      ∀ D : ℝ, 60 ≤ D → MomentDuhamelCut.MomentHypCut (sample d) E s t D)
    (hcut : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → WindowLeft s C → ∀ c : ℝ, 0 < c → Cond272Reg (band d) E s t c →
      BoundsCore (sample d) E s → CutHypEvOnSlot (sample d) E s t)
    (h514 : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg (band d) E s t c → ∀ n : ℕ, 2 ≤ n →
      Step3.Lemma514 (band d).P (Step3.flowXiLK (sample d) E s t)
        (Step3.flowXiL (sample d) E s t) (Step3.flowA (band d) E s t) n)
    (h45i : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg (band d) E s t c →
      Eq45FlowInputs (sample d) E s t)
    (h548e : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → WindowLeft s C → ∀ c : ℝ, 0 < c → Cond272Reg (band d) E s t c →
      Eq548EntryDataEvOn' (sample d) E s t) :
    Thm221NoELFrom (sample d) κ C where
  step E hE c hc0 s t hs0 hst ht1 hw hreg hB :=
    boundsCore_step_of_inputs_mergedOn (sample d) hκ0 hκ1 hE hs0 hst ht1 hc0 hreg hB
      (step1Hyp_slot d hκ0 E hE s t hs0 hst ht1 c hc0 hreg hB)
      (Hy E hE s t hs0 hst ht1 c hc0 hreg) (hcut E hE s t hs0 hst ht1 hw c hc0 hreg hB)
      (h514 E hE s t hs0 hst ht1 c hc0 hreg) (h45i E hE s t hs0 hst ht1 c hc0 hreg)
      (h548e E hE s t hs0 hst ht1 hw c hc0 hreg)

/-- **T245's table implies this one** — the compiled certificate that both halves of T249's
repair are *free*: the event restriction (`RBM.MomentDuhamelCut.CutHypEvOn.of_cutHypEv`,
`RBM.Eq548EntryDataEv.toEvOn'`) and the `RBM.WindowLeft` premise (an extra antecedent on an
assumed implication) each only weaken a slot, and `RBM.Thm221NoEL.toFrom` weakens the
conclusion.  So nothing in this section can be harder to satisfy than
`RBM.Gauss.thm221NoEL_of_inputs_merged_gauss`. -/
theorem thm221NoEL_of_inputs_mergedOn_gauss_of_unrestricted (d : Dims) {κ : ℝ} (hκ0 : 0 < κ)
    (hκ1 : κ ≤ 1) (C : ℝ)
    (Hy : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg (band d) E s t c →
      ∀ D : ℝ, 60 ≤ D → MomentDuhamelCut.MomentHypCut (sample d) E s t D)
    (hcut : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg (band d) E s t c →
      BoundsCore (sample d) E s →
      MomentDuhamelCut.CutHypEv (band d).P (fun N u ω => (sample d).xiLK E N u ω 2) s t
        (fun N => Step3.flowAs (band d) E s N ^ ((1 : ℝ) / 2)))
    (h514 : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg (band d) E s t c → ∀ n : ℕ, 2 ≤ n →
      Step3.Lemma514 (band d).P (Step3.flowXiLK (sample d) E s t)
        (Step3.flowXiL (sample d) E s t) (Step3.flowA (band d) E s t) n)
    (h45i : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg (band d) E s t c →
      Eq45FlowInputs (sample d) E s t)
    (h548e : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg (band d) E s t c →
      Eq548EntryDataEv (sample d) E s t) :
    Thm221NoELFrom (sample d) κ C :=
  (thm221NoEL_of_inputs_merged_gauss d hκ0 hκ1 Hy hcut h514 h45i h548e).toFrom C

end MergedOnGauss

/-! ### 11. T251: satisfiability of the new premise

`RBM.WindowLeft` must not be a premise that nothing meets.  Two compiled facts pin it down on
the paper's own grid.  Together with `RBM.not_windowLeft_zero` they say exactly which cells of
p. 24's grid the repaired chain covers: all of them except the first. -/

section WindowLeftWitness

open Filter

/-- **The new premise is met on every cell of p. 24's grid except the first**, jointly with
everything the merged step needs there.

At `E = 0` on T202's explicit model `RBM.Gauss.Dims.exampleGrow` and the paper's own right end
`t_N = 1 - N^{-1/2}`, for every `k`, the cell `(u_{k+1}, u_{k+2})` satisfies all four domain conditions of
`RBM.Thm221NoELFrom.step` — `0 ≤ u_{k+1}`, `u_{k+1} ≤ u_{k+2}`, `u_{k+2} < 1` and
`RBM.Cond272Reg` with the same `c > 0`, chosen before `E` and `t` — **and** the new premise
`RBM.WindowLeft … C`, for every `C > 0`.  So the premise added in §§9–10 is not vacuous, and
it is compatible with everything the step already asks for. -/
theorem windowLeft_grid_witness {C : ℝ} (hC : 0 < C) :
    ∃ τ' : ℝ, 0 < τ' ∧ ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ,
      WindowLeft (fun N => gridT (((band Dims.exampleGrow).W N : ℝ)) τ'
        (1 - (N : ℝ) ^ (-(1 : ℝ) / 2)) (k + 1)) C ∧
      (∀ N : ℕ, 0 ≤ gridT (((band Dims.exampleGrow).W N : ℝ)) τ'
        (1 - (N : ℝ) ^ (-(1 : ℝ) / 2)) (k + 1)) ∧
      (∀ N : ℕ, gridT (((band Dims.exampleGrow).W N : ℝ)) τ'
          (1 - (N : ℝ) ^ (-(1 : ℝ) / 2)) (k + 1) ≤
        gridT (((band Dims.exampleGrow).W N : ℝ)) τ'
          (1 - (N : ℝ) ^ (-(1 : ℝ) / 2)) (k + 2)) ∧
      (∀ N : ℕ, gridT (((band Dims.exampleGrow).W N : ℝ)) τ'
        (1 - (N : ℝ) ^ (-(1 : ℝ) / 2)) (k + 2) < 1) ∧
      Cond272Reg (band Dims.exampleGrow) 0
        (fun N => gridT (((band Dims.exampleGrow).W N : ℝ)) τ'
          (1 - (N : ℝ) ^ (-(1 : ℝ) / 2)) (k + 1))
        (fun N => gridT (((band Dims.exampleGrow).W N : ℝ)) τ'
          (1 - (N : ℝ) ^ (-(1 : ℝ) / 2)) (k + 2)) c := by
  set t : ℕ → ℝ := fun N => 1 - (N : ℝ) ^ (-(1 : ℝ) / 2) with ht_def
  have ht0 : ∀ N : ℕ, 0 ≤ t N := by
    intro N
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · subst h0
      simp [ht_def, Real.zero_rpow (by norm_num : (-(1 : ℝ) / 2) ≠ 0)]
    · have h1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast h0
      have : ((N : ℝ)) ^ (-(1 : ℝ) / 2) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos h1 (by norm_num)
      simp only [ht_def]
      linarith
  have htτ : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-1 + (1 : ℝ) / 2) ≤ 1 - t N := by
    filter_upwards with N
    simp only [ht_def, sub_sub_cancel]
    norm_num
  have htlb : ∀ᶠ N : ℕ in atTop, (1 : ℝ) / 2 ≤ t N := by
    filter_upwards [eventually_ge_atTop 4] with N hN
    have h4 : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have h1 : ((N : ℝ)) ^ (-(1 : ℝ) / 2) ≤ ((4 : ℝ)) ^ (-(1 : ℝ) / 2) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) h4 (by norm_num)
    have h2 : ((4 : ℝ)) ^ (-(1 : ℝ) / 2) = 1 / 2 := by
      rw [show (-(1 : ℝ) / 2) = -((1 : ℝ) / 2) by ring, Real.rpow_neg (by norm_num),
        show ((4 : ℝ)) ^ ((1 : ℝ) / 2) = 2 from by
          rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, ← Real.rpow_natCast (2 : ℝ) 2,
            ← Real.rpow_mul (by norm_num)]
          norm_num]
      norm_num
    simp only [ht_def]
    linarith
  obtain ⟨τ', hτ'0, c, hc0, n₀, hgrid⟩ :=
    cond272Reg_grid_step_domain (band Dims.exampleGrow) (κ := 1) (τ := (1 : ℝ) / 2) one_pos
      (by norm_num)
  obtain ⟨-, hstep⟩ := hgrid 0 (by norm_num) t ht0 htτ
  exact ⟨τ', hτ'0, c, hc0, fun k =>
    ⟨windowLeft_gridT_succ (band Dims.exampleGrow) hτ'0 (by norm_num : (0 : ℝ) < 1 / 2)
        htlb hC k,
      (hstep (k + 1)).1, (hstep (k + 1)).2.1, (hstep (k + 1)).2.2.1,
      (hstep (k + 1)).2.2.2⟩⟩

end WindowLeftWitness

end Gauss

/-! ### 12. Deviations from the paper introduced here (T251)

**`T251a` — the window of (5.48) is asked with a left endpoint `s_N ≥ N^{-C}`, and the
deterministic modulus only on a high-probability event.**

① **Paper location.**  §5.3: the far-martingale estimate (5.48), whose chaining argument is
set up at (5.43) and (5.46); and the induction grid of p. 24, `1 - s_k = W^{-kτ'}`, whose
first point is `s_0 = 0`.

② **Is the paper wrong / must it change?**  Yes, a remark has to be added.  The continuity
argument behind (5.46)–(5.48) needs a modulus of continuity for `u ↦ J*^{sm}_{u,D}` on the
whole window, and along the flow `H_u = √u X` that modulus has constant `O(‖X‖/√s)`.  Two
things follow, both of which the printed text leaves implicit:
  * the estimate cannot be asked at every sample point (`‖X‖` is unbounded) — it has to be
    restricted to an event of high probability, which is why `RBM.Eq548EntryDataEvOn'` carries
    `Good` and `RBM.HighProb`;
  * it cannot be asked on a window whose left endpoint is `0` — T249's
    `RBM.not_entryModulusEv_swapSample_of_far` is a compiled refutation, and the mechanism is
    the paper's own (2.67): at `u = 0` the loop equals its primitive value for **every** `ω`,
    so `J*^{sm}_{0,D} ≡ 1`, while for every `v > 0` the functional already moves by an
    `O(1)` amount at some sample point.
  Hence `RBM.WindowLeft s C`, and hence `RBM.Thm221NoELFrom` rather than `RBM.Thm221NoEL`:
  the first cell `u_0 = 0 → u_1` of the p. 24 grid (`RBM.not_windowLeft_gridT_zero`) is not
  covered by this chain, while every later cell is (`RBM.windowLeft_gridT_succ`).  The paper
  needs one added sentence saying how `[0, u_1]` is handled — (2.67) gives the *left endpoint*
  only, not the step.

③ **Size of the change.**  About four lines near (5.46) (restrict to `Ω_N = {‖X‖ ≤ N}` and
state the modulus there), plus one sentence on p. 24 for the first grid cell.

④ **Renumbering.**  None: nothing is inserted before an existing numbered display.
-/

end RBM
