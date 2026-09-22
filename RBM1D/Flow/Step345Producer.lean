/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Flow.Thm221NoEL
import RBM1D.Gauss.Eq45Flow

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

end RBM
