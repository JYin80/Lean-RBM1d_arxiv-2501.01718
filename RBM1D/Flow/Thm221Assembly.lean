/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Flow.Thm221NoEL
import RBM1D.Hierarchy.Step2FarMart

/-!
# Theorem 2.21, first pass: the assembly file (T239)

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, §2.7 and §5.3.

`RBM.thm221NoEL_of_inputs_W` (`Flow/Thm221NoEL.lean`, T233) takes six named inputs, the sixth
being (5.48) in the smoothed shape `RBM.FlowEq548Sm`.  T228 built producers for exactly that
shape in `Hierarchy/Step2FarMart.lean` — `RBM.Step2FarMart.flowEq548W_of_cutHyp` and
`RBM.Step2FarMart.flowEq548W_of_entries`, at the concrete weight
`RBM.Step2FarMart.nearChi`, whose far vanishing is
`RBM.Step2FarMart.eventually_nearChi_eq_zero`.

The two halves never met: `Flow/Thm221NoEL.lean` and `Hierarchy/Step2FarMart.lean` are both
import leaves, joined only by the root `RBM1D.lean`.  **This file is the join**: it imports
both and changes neither, and it is where the remaining named hypotheses of the first pass are
to be discharged as producers for them appear.

## Main results

* `RBM.flowEq548Sm_of_nearChi` — the bridge: `RBM.Step45.FlowEq548W` at the weight
  `RBM.Step2FarMart.nearChi` **is** `RBM.FlowEq548Sm`, its far-vanishing side supplied by
  `RBM.Step2FarMart.eventually_nearChi_eq_zero`.  Nothing here weakens a conclusion: the
  package `RBM.FlowEq548Sm` sits in a *hypothesis* slot of
  `RBM.thm221NoEL_of_inputs_W`, and it is the weaker of the two forms
  (`RBM.flowEq548Sm_of_flowEq548`), so filling it from the smoothed producer is sound.
* `RBM.flowEq548Sm_of_cutHyp`, `RBM.flowEq548Sm_of_entries` — the same for T228's two
  producers, so the (5.48) slot can be filled from a `RBM.MomentDuhamelCut.CutHyp` for
  `RBM.Step2FarMart.jSfarSm`, or from entrywise data on `L - K`.
* `RBM.Eq548EntryData` — the entrywise package of `RBM.Step2FarMart.flowEq548W_of_entries`,
  bundled so that the assembled hypothesis table stays readable, and
  `RBM.flowEq548Sm_of_entryData`.
* `RBM.thm221NoEL_of_inputs_entries` — **the assembly**: `RBM.Thm221NoEL X κ` (D13's shape,
  (2.71) removed from hypothesis and conclusion) from Steps 1–5's five remaining named inputs
  **plus the entrywise data of (5.48)**.  The (5.48) item `RBM.FlowEq548Sm` no longer occurs
  in its hypothesis list.
* `RBM.thm221NoEL_of_inputs_cutHyp` — the same, stopping one level earlier, at a `CutHyp` for
  `RBM.Step2FarMart.jSfarSm`.
* `RBM.thm221Assembly_hyp_consistent`, `RBM.thm221Assembly_far_critical` — the
  satisfiability checks of §3.

## What this file does **not** close

The five other named inputs of Steps 1–5 (`RBM.Step1.Hyp`,
`RBM.MomentDuhamelCut.MomentHypCut`, the Step-3 `≺` input, `RBM.Step3.Lemma514`,
`RBM.StepGlue.Eq45Flow`) and, inside the (5.48) item, the three fields of T228 that have no
producer yet (`hmeas`, `hmod`, `hmoment`) and the initial bound `hinit` are **still
hypotheses**, listed as such in the signature of `RBM.thm221NoEL_of_inputs_entries`.  They are
not hidden behind a bundle that no object satisfies — see §3.

## Deviations from the paper

None: this file only composes statements already in the tree.
-/

namespace RBM

open Filter MeasureTheory

/-! ### 1. The bridge: T228's producers fill the (5.48) slot -/

section Bridge

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E : ℝ} {s t : ℕ → ℝ}

/-- **The bridge of T239.**  `RBM.Step45.FlowEq548W` at the concrete smooth weight
`RBM.Step2FarMart.nearChi` is exactly the package `RBM.FlowEq548Sm` that
`RBM.thm221NoEL_of_inputs_W` consumes: the existential witness is the weight itself and its
far-vanishing side is `RBM.Step2FarMart.eventually_nearChi_eq_zero`.

This is the one declaration the two import leaves could not host. -/
theorem flowEq548Sm_of_nearChi (X : Sample B) (ht1 : ∀ N, t N < 1)
    (h : Step45.FlowEq548W X E s t
      (fun N p => Step2FarMart.nearChi (B.W N : ℝ) (B.ell N p.1)
        (zdist (B.L N) (p.2.1 - p.2.2)))) :
    FlowEq548Sm X E s t :=
  ⟨fun N p => Step2FarMart.nearChi (B.W N : ℝ) (B.ell N p.1) (zdist (B.L N) (p.2.1 - p.2.2)),
    Step2FarMart.eventually_nearChi_eq_zero (s := s) ht1, h⟩

/-- **The (5.48) slot from the bootstrap interface** — `RBM.Step2FarMart.flowEq548W_of_cutHyp`
through the bridge. -/
theorem flowEq548Sm_of_cutHyp (X : Sample B) (ht1 : ∀ N, t N < 1)
    (hnear : ∀ D : ℝ, 0 < D → StochDom B.P
      (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
        X.lkErr E N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => (etaT E (s N) / etaT E p.1) ^ 2 *
        tailT (B.W N : ℝ) (B.ell N p.1) (etaT E p.1) D
          (zdist (B.L N) (p.2.1 - p.2.2))))
    (H : ∀ D : ℝ, 0 < D →
      MomentDuhamelCut.CutHyp B.P (fun N u ω => Step2FarMart.jSfarSm X E D N u ω) s t
        (fun _ => 1))
    (hinit : ∀ D : ℝ, 0 < D → StochDom B.P
      (fun N (_ : Unit) ω => Step2FarMart.jSfarSm X E D N (s N) ω) (fun _ _ _ => (1 : ℝ))) :
    FlowEq548Sm X E s t :=
  flowEq548Sm_of_nearChi X ht1 (Step2FarMart.flowEq548W_of_cutHyp X hnear H hinit)

end Bridge

/-! ### 2. The entrywise package, and the assembly

`RBM.Step2FarMart.flowEq548W_of_entries` takes five pieces of data.  Bundling them is only a
readability measure — `RBM.Eq548EntryData` is a `Prop`-valued structure whose five fields are
verbatim the five hypotheses of that theorem, and `RBM.flowEq548Sm_of_entryData` unbundles
them again. -/

section Entries

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- **The entrywise data of (5.48)** (T228, `RBM.Step2FarMart.flowEq548W_of_entries`),
bundled.  Five fields, all still hypotheses of the first pass:

* `near` — the sharp near half (5.47);
* `meas` — measurability of `RBM.Step2FarMart.jSfarSm` in `ω` at each fixed time;
* `modulus` — the entrywise two-sided modulus of `L - K` (the field §10 of T228 reduced to the
  entries; it is **false** for the unsmoothed `jSfar`);
* `moment` — the truncated moment bound on the net (T210 located the obstruction: the first
  pass has to bootstrap the prefix event);
* `init` — the initial bound at `u = s_N`, i.e. (2.68)/(2.69) at the left endpoint.

Everything else in `RBM.MomentDuhamelCut.CutHyp` — `window`, `Θ_pos`, `J_nonneg`, `mesh_pos`,
`mesh_fine`, `card_le`, `modulus` at `Kmod = 1`, `γ = 1/2` — is discharged by
`RBM.Step2FarMart.cutHyp_jSfarSm_of_entries`, so the `mesh_fine`/`card_le` pair cannot make
the bundle unsatisfiable. -/
structure Eq548EntryData (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) : Prop where
  near : ∀ D : ℝ, 0 < D → StochDom B.P
    (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
      X.lkErr E N p.1 ω (pmLoop p.2.1 p.2.2))
    (fun N p _ => (etaT E (s N) / etaT E p.1) ^ 2 *
      tailT (B.W N : ℝ) (B.ell N p.1) (etaT E p.1) D (zdist (B.L N) (p.2.1 - p.2.2)))
  meas : ∀ D : ℝ, 0 < D → ∀ (N : ℕ) (u : ℝ),
    AEStronglyMeasurable (fun ω => Step2FarMart.jSfarSm X E D N u ω) B.P
  modulus : ∀ D : ℝ, 0 < D → ∀ (N : ℕ) (ω : Ω), ∀ v ∈ Set.Icc (s N) (t N),
    ∀ w ∈ Set.Icc (s N) (t N), ∀ x : LoopArg (B.L N) 2,
      15 / 8 * |(zdist (B.L N) (x 0 - x 1) : ℝ) / (6 * ellStar (B.W N : ℝ) (B.ell N v))
            - (zdist (B.L N) (x 0 - x 1) : ℝ) / (6 * ellStar (B.W N : ℝ) (B.ell N w))|
          * |‖Step2.lk X E N v ω x‖ / tailT (B.W N : ℝ) (B.ell N v) (etaT E v) D
              (zdist (B.L N) (x 0 - x 1))|
        + |‖Step2.lk X E N v ω x‖ / tailT (B.W N : ℝ) (B.ell N v) (etaT E v) D
              (zdist (B.L N) (x 0 - x 1))
            - ‖Step2.lk X E N w ω x‖ / tailT (B.W N : ℝ) (B.ell N w) (etaT E w) D
              (zdist (B.L N) (x 0 - x 1))|
          ≤ (N : ℝ) ^ (1 : ℝ) * |v - w| ^ ((1 : ℝ) / 2)
  moment : ∀ D : ℝ, 0 < D → ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ ε > (0 : ℝ), ∀ p : ℕ, ∃ C > (0 : ℝ),
    ∀ᶠ N : ℕ in atTop,
    ∀ ws ∈ MomentDuhamelCut.netFinset s t (fun N => ((N : ℝ) + 1) ^ (2 : ℝ)) N,
      ∫ ω, |MomentDuhamelCut.cutTrunc ((N : ℝ) ^ (2 * δ) * 1)
            (Step2FarMart.jSfarSm X E D N ws ω)| ^ (2 * p) ∂B.P
        ≤ C * ((N : ℝ) ^ (ε * p) * (1 : ℝ) ^ (2 * p))
  init : ∀ D : ℝ, 0 < D → StochDom B.P
    (fun N (_ : Unit) ω => Step2FarMart.jSfarSm X E D N (s N) ω) (fun _ _ _ => (1 : ℝ))

variable {E : ℝ} {s t : ℕ → ℝ}

/-- **The (5.48) slot from entrywise data** — `RBM.Step2FarMart.flowEq548W_of_entries` through
the bridge. -/
theorem flowEq548Sm_of_entryData (X : Sample B) (hst : ∀ N, s N ≤ t N) (hs0 : ∀ N, 0 ≤ s N)
    (ht1 : ∀ N, t N < 1) (H : Eq548EntryData X E s t) :
    FlowEq548Sm X E s t :=
  flowEq548Sm_of_nearChi X ht1
    (Step2FarMart.flowEq548W_of_entries X hst hs0 ht1 H.near H.meas H.modulus H.moment H.init)

/-- Also available one level down, for a producer that prefers to supply the five hypotheses
unbundled. -/
theorem flowEq548Sm_of_entries (X : Sample B) (hst : ∀ N, s N ≤ t N) (hs0 : ∀ N, 0 ≤ s N)
    (ht1 : ∀ N, t N < 1)
    (hnear : ∀ D : ℝ, 0 < D → StochDom B.P
      (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
        X.lkErr E N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => (etaT E (s N) / etaT E p.1) ^ 2 *
        tailT (B.W N : ℝ) (B.ell N p.1) (etaT E p.1) D
          (zdist (B.L N) (p.2.1 - p.2.2))))
    (hmeas : ∀ D : ℝ, 0 < D → ∀ (N : ℕ) (u : ℝ),
      AEStronglyMeasurable (fun ω => Step2FarMart.jSfarSm X E D N u ω) B.P)
    (hmod : ∀ D : ℝ, 0 < D → ∀ (N : ℕ) (ω : Ω), ∀ v ∈ Set.Icc (s N) (t N),
      ∀ w ∈ Set.Icc (s N) (t N), ∀ x : LoopArg (B.L N) 2,
        15 / 8 * |(zdist (B.L N) (x 0 - x 1) : ℝ) / (6 * ellStar (B.W N : ℝ) (B.ell N v))
              - (zdist (B.L N) (x 0 - x 1) : ℝ) / (6 * ellStar (B.W N : ℝ) (B.ell N w))|
            * |‖Step2.lk X E N v ω x‖ / tailT (B.W N : ℝ) (B.ell N v) (etaT E v) D
                (zdist (B.L N) (x 0 - x 1))|
          + |‖Step2.lk X E N v ω x‖ / tailT (B.W N : ℝ) (B.ell N v) (etaT E v) D
                (zdist (B.L N) (x 0 - x 1))
              - ‖Step2.lk X E N w ω x‖ / tailT (B.W N : ℝ) (B.ell N w) (etaT E w) D
                (zdist (B.L N) (x 0 - x 1))|
            ≤ (N : ℝ) ^ (1 : ℝ) * |v - w| ^ ((1 : ℝ) / 2))
    (hmoment : ∀ D : ℝ, 0 < D → ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ ε > (0 : ℝ), ∀ p : ℕ,
      ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      ∀ ws ∈ MomentDuhamelCut.netFinset s t (fun N => ((N : ℝ) + 1) ^ (2 : ℝ)) N,
        ∫ ω, |MomentDuhamelCut.cutTrunc ((N : ℝ) ^ (2 * δ) * 1)
              (Step2FarMart.jSfarSm X E D N ws ω)| ^ (2 * p) ∂B.P
          ≤ C * ((N : ℝ) ^ (ε * p) * (1 : ℝ) ^ (2 * p)))
    (hinit : ∀ D : ℝ, 0 < D → StochDom B.P
      (fun N (_ : Unit) ω => Step2FarMart.jSfarSm X E D N (s N) ω) (fun _ _ _ => (1 : ℝ))) :
    FlowEq548Sm X E s t :=
  flowEq548Sm_of_entryData X hst hs0 ht1
    ⟨hnear, hmeas, hmod, hmoment, hinit⟩

end Entries

/-! ### 3. Theorem 2.21 (first pass) with the (5.48) item discharged -/

section Assembly

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- **Theorem 2.21 without (2.71), in D13's shape, with the (5.48) item replaced by T228's
entrywise data.**

Verbatim `RBM.thm221NoEL_of_inputs_W` except in the last slot: where that theorem asks for
`RBM.FlowEq548Sm X E s t`, this one asks for `RBM.Eq548EntryData X E s t` and produces the
(5.48) package itself, through `RBM.flowEq548Sm_of_entryData`.  So **`RBM.FlowEq548Sm` and
`RBM.Step45.FlowEq548` do not occur in the hypothesis list at all**.

Nothing is weakened: `RBM.FlowEq548Sm` occupied a hypothesis position, and the substitute is a
theorem producing it, not a restatement of the conclusion. -/
theorem thm221NoEL_of_inputs_entries (X : Sample B) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (h1 : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg B E s t c → Step1.Hyp X E s t)
    (Hy : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg B E s t c →
      ∀ D : ℝ, 60 ≤ D → MomentDuhamelCut.MomentHypCut X E s t D)
    (hΘ : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg B E s t c →
      StochDom B.P (Step3.flowXiLK X E s t 2)
        (fun N (_ : TimeIcc s t N) (_ : Ω) => Step3.flowAs B E s N ^ ((1 : ℝ) / 2)))
    (h514 : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg B E s t c → ∀ n : ℕ, 2 ≤ n →
      Step3.Lemma514 B.P (Step3.flowXiLK X E s t) (Step3.flowXiL X E s t)
        (Step3.flowA B E s t) n)
    (h45 : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg B E s t c → StepGlue.Eq45Flow X E s t)
    (h548e : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg B E s t c → Eq548EntryData X E s t) :
    Thm221NoEL X κ :=
  thm221NoEL_of_inputs_W X hκ0 hκ1 h1 Hy hΘ h514 h45
    fun E hE s t hs0 hst ht1 c hc0 hreg =>
      flowEq548Sm_of_entryData X hst hs0 ht1 (h548e E hE s t hs0 hst ht1 c hc0 hreg)

/-- The same assembly stopping one level earlier, at a `RBM.MomentDuhamelCut.CutHyp` for
`RBM.Step2FarMart.jSfarSm` at the critical threshold `Θ ≡ 1` — the interface of
`RBM.Step2FarMart.flowEq548W_of_cutHyp`. -/
theorem thm221NoEL_of_inputs_cutHyp (X : Sample B) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (h1 : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg B E s t c → Step1.Hyp X E s t)
    (Hy : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg B E s t c →
      ∀ D : ℝ, 60 ≤ D → MomentDuhamelCut.MomentHypCut X E s t D)
    (hΘ : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg B E s t c →
      StochDom B.P (Step3.flowXiLK X E s t 2)
        (fun N (_ : TimeIcc s t N) (_ : Ω) => Step3.flowAs B E s N ^ ((1 : ℝ) / 2)))
    (h514 : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg B E s t c → ∀ n : ℕ, 2 ≤ n →
      Step3.Lemma514 B.P (Step3.flowXiLK X E s t) (Step3.flowXiL X E s t)
        (Step3.flowA B E s t) n)
    (h45 : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg B E s t c → StepGlue.Eq45Flow X E s t)
    (hnear : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg B E s t c →
      ∀ D : ℝ, 0 < D → StochDom B.P
        (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
          X.lkErr E N p.1 ω (pmLoop p.2.1 p.2.2))
        (fun N p _ => (etaT E (s N) / etaT E p.1) ^ 2 *
          tailT (B.W N : ℝ) (B.ell N p.1) (etaT E p.1) D
            (zdist (B.L N) (p.2.1 - p.2.2))))
    (hcut : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg B E s t c → ∀ D : ℝ, 0 < D →
      MomentDuhamelCut.CutHyp B.P (fun N u ω => Step2FarMart.jSfarSm X E D N u ω) s t
        (fun _ => 1))
    (hinit : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg B E s t c → ∀ D : ℝ, 0 < D →
      StochDom B.P (fun N (_ : Unit) ω => Step2FarMart.jSfarSm X E D N (s N) ω)
        (fun _ _ _ => (1 : ℝ))) :
    Thm221NoEL X κ :=
  thm221NoEL_of_inputs_W X hκ0 hκ1 h1 Hy hΘ h514 h45
    fun E hE s t hs0 hst ht1 c hc0 hreg =>
      flowEq548Sm_of_cutHyp X ht1 (hnear E hE s t hs0 hst ht1 c hc0 hreg)
        (hcut E hE s t hs0 hst ht1 c hc0 hreg) (hinit E hE s t hs0 hst ht1 c hc0 hreg)

end Assembly

/-! ### 4. Satisfiability of the assembled hypothesis table

Three failure modes to rule out, in the order `docs/STATUS.md` lists them.

**The substitution does not weaken anything.**  `RBM.FlowEq548Sm` sat in a *hypothesis*
position of `RBM.thm221NoEL_of_inputs_W`; what replaces it is a *theorem producing it*
(`RBM.flowEq548Sm_of_entryData`), and the conclusion `RBM.Thm221NoEL X κ` is unchanged —
`RBM.thm221Assembly_conclusion_unchanged` below is the `rfl`-probe.  The direction of
`RBM.flowEq548Sm_of_flowEq548` (sharp ⟹ smoothed) is the safe one for a hypothesis slot.

**The domain is non-empty, at a non-degenerate scale.**  `RBM.cond272Reg_grid_step_domain`
supplies all four domain conditions `0 ≤ s`, `s ≤ t`, `t < 1`, `RBM.Cond272Reg … c` at every
step of the paper's grid with one and the same `c > 0`, chosen before `E` and `t`; and its
first conjunct pins the grid to `t` at `k = n₀`, so the window is not the collapsed `s = t`.
`RBM.boundsCore_gauss_witness` then supplies the remaining input of the step — the hypothesis
`RBM.BoundsCore X E s` — on T202's explicit band model, at the scale `W ℓ_0 η_0 ≥ N^{1/2}`.
`RBM.thm221Assembly_hyp_consistent` puts the two together.

**The (5.48) item is not fiat and not vacuous.**  `RBM.Step2FarMart.one_le_jSfarSm` holds for
**every** `ω`, the degenerate `ω = 0` included, so the far request `jSfarSm ≺ 1` is critical
and not something `0` meets; the near prefactor at the critical grid point is the genuinely
large `(N+1)²`; and the `mesh_fine`/`card_le` pair of the bundle is *proved*, not assumed, by
`RBM.Step2FarMart.cutHyp_jSfarSm_of_entries`.
`RBM.thm221Assembly_far_critical` compiles the `ω = 0` instance.

**Time quantifier.**  Every asymptotic side condition entering the (5.48) item is
`∀ᶠ N in atTop` *inside* the statement — `RBM.Step2FarMart.eventually_nearChi_eq_zero`, which
is what `RBM.Step45.decay_of_split_W` consumes, and the `moment` field — with `D`, `δ`, `ε`
and `p` fixed first.  No `∀ p, ∀ N` order occurs. -/

section Satisfiable

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The conclusion did not change.**  The assembled theorem and T233's
`RBM.thm221NoEL_of_inputs_W` end at the same `RBM.Thm221NoEL X κ`, and the assembled one is
literally the latter with the (5.48) slot filled. -/
theorem thm221Assembly_conclusion_unchanged {B : Band Ω} (X : Sample B) {κ : ℝ} (hκ0 : 0 < κ)
    (hκ1 : κ ≤ 1)
    (h1 : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg B E s t c → Step1.Hyp X E s t)
    (Hy : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg B E s t c →
      ∀ D : ℝ, 60 ≤ D → MomentDuhamelCut.MomentHypCut X E s t D)
    (hΘ : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg B E s t c →
      StochDom B.P (Step3.flowXiLK X E s t 2)
        (fun N (_ : TimeIcc s t N) (_ : Ω) => Step3.flowAs B E s N ^ ((1 : ℝ) / 2)))
    (h514 : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg B E s t c → ∀ n : ℕ, 2 ≤ n →
      Step3.Lemma514 B.P (Step3.flowXiLK X E s t) (Step3.flowXiL X E s t)
        (Step3.flowA B E s t) n)
    (h45 : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg B E s t c → StepGlue.Eq45Flow X E s t)
    (h548e : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg B E s t c → Eq548EntryData X E s t) :
    thm221NoEL_of_inputs_entries X hκ0 hκ1 h1 Hy hΘ h514 h45 h548e =
      thm221NoEL_of_inputs_W X hκ0 hκ1 h1 Hy hΘ h514 h45
        (fun E hE s t hs0 hst ht1 c hc0 hreg =>
          flowEq548Sm_of_entryData X hst hs0 ht1 (h548e E hE s t hs0 hst ht1 c hc0 hreg)) :=
  rfl

/-- **The step's domain and its `RBM.BoundsCore` input are jointly satisfiable, on the paper's
own grid and T202's explicit band model.**

`RBM.cond272Reg_grid_step_domain` gives `τ' > 0`, `c > 0`, `n₀` — chosen from `κ, τ` alone and
*before* `E` and `t` — such that at every `k` all four domain conditions of
`RBM.Thm221NoEL.step` hold on the grid `u_k = min(1 - W^{-kτ'}, t)`; the first conjunct pins
the grid to `t` at `k = n₀`, so the window is not the collapsed one.  The last two conjuncts
are the fifth input of the step, `RBM.BoundsCore X E s` at the start `s ≡ 0` of the induction,
and the certificate that the start is at the critical scale `W ℓ_0 η_0 ≥ N^{1/2}` rather than a
degenerate one.

So the assembled hypothesis table of `RBM.thm221NoEL_of_inputs_entries` is not jointly
unsatisfiable on account of its *domain*; the five named inputs and the four open fields of
`RBM.Eq548EntryData` remain hypotheses, as the signature says. -/
theorem thm221Assembly_hyp_consistent {τ : ℝ} (hτ0 : 0 < τ) :
    ∃ τ' : ℝ, 0 < τ' ∧ ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ,
      ∀ t : ℕ → ℝ, (∀ N, 0 ≤ t N) →
        (∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-1 + τ) ≤ 1 - t N) →
        (∀ᶠ N : ℕ in atTop,
          gridT ((Gauss.band Gauss.Dims.exampleGrow).W N) τ' (t N) n₀ = t N) ∧
        (∀ k : ℕ,
          (∀ N, 0 ≤ gridT ((Gauss.band Gauss.Dims.exampleGrow).W N) τ' (t N) k) ∧
          (∀ N, gridT ((Gauss.band Gauss.Dims.exampleGrow).W N) τ' (t N) k ≤
            gridT ((Gauss.band Gauss.Dims.exampleGrow).W N) τ' (t N) (k + 1)) ∧
          (∀ N, gridT ((Gauss.band Gauss.Dims.exampleGrow).W N) τ' (t N) (k + 1) < 1) ∧
          Cond272Reg (Gauss.band Gauss.Dims.exampleGrow) 0
            (fun N => gridT ((Gauss.band Gauss.Dims.exampleGrow).W N) τ' (t N) k)
            (fun N => gridT ((Gauss.band Gauss.Dims.exampleGrow).W N) τ' (t N) (k + 1)) c) ∧
        BoundsCore (Gauss.sample Gauss.Dims.exampleGrow) 0 (fun _ => 0) ∧
        (∀ᶠ N : ℕ in atTop, (N : ℝ) ^ ((1 : ℝ) / 2) ≤
          (Gauss.band Gauss.Dims.exampleGrow).scale 0 N 0) := by
  obtain ⟨τ', hτ'0, c, hc0, n₀, hgrid⟩ :=
    cond272Reg_grid_step_domain (Gauss.band Gauss.Dims.exampleGrow)
      (κ := 1) (τ := τ) one_pos hτ0
  refine ⟨τ', hτ'0, c, hc0, n₀, fun t ht0 ht => ?_⟩
  obtain ⟨hlast, hstep⟩ := hgrid 0 (by norm_num) t ht0 ht
  exact ⟨hlast, hstep, boundsCore_gauss_witness.1, boundsCore_gauss_witness.2⟩

/-- **The (5.48) item is critical at the degenerate sample point `ω = 0`.**

The audit rule of `docs/STATUS.md` (T164): a pointwise hypothesis on a random model has to be
checked at `ω = 0`, where `H = 0`.  The far half of `RBM.Eq548EntryData` is
`jSfarSm ≺ 1`, and `RBM.Step2FarMart.one_le_jSfarSm` says `1 ≤ jSfarSm` *for every* `ω`,
`ω = 0` included — so the request is exactly critical there and cannot be met by a degenerate
functional.  Together with the two accompanying non-degeneracy facts (the near prefactor
`(N+1)²` at the critical grid point, and `mesh_fine`/`card_le` at equality) this is the `ω = 0`
instance of `RBM.Step2FarMart.smooth_route_nondegenerate`, stated for **every** `ω` (which is
strictly stronger than checking the one degenerate point). -/
theorem thm221Assembly_far_critical {B : Band Ω} (X : Sample B) {E : ℝ}
    (hE : |E| < 2) {D : ℝ} {N : ℕ} {u : ℝ} (hN : 2 ≤ N) :
    (∀ ω : Ω, 1 ≤ Step2FarMart.jSfarSm X E D N u ω) ∧
      (etaT E (Step2FarMart.sGrid N) / etaT E (Step2FarMart.tGrid N)) ^ 2 = ((N : ℝ) + 1) ^ 2 ∧
      ((N : ℝ) ^ (1 : ℝ) * (1 / (N : ℝ) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) = 1 ∧
        ((1 : ℝ) - 0) * (N : ℝ) ^ (2 : ℝ) + 2 ≤ (N : ℝ) ^ (3 : ℝ)) :=
  ⟨fun ω => Step2FarMart.one_le_jSfarSm X (E := E) (D := D) (N := N) (u := u) (ω := ω),
    Step2FarMart.pref_grid_critical hE N, Step2FarMart.sat_mesh_card_at_one hN⟩

end Satisfiable

end RBM
