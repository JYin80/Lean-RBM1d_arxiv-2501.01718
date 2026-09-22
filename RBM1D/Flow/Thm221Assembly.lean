/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Flow.Thm221NoEL
import RBM1D.Hierarchy.Step2FarMart
import RBM1D.Flow.Eq548Producer

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
  satisfiability checks of §4.
* `RBM.inv_sq_mul_decayProf_le_tT`, `RBM.stochDom_jSfarSm_init_of_boundsCore` — **T241**: the
  producer of `RBM.Eq548EntryData.init`.  The left endpoint `J*^{sm}_{s_N,D} ≺ 1` of the
  (5.48) bootstrap is (2.69) at `u = s_N`, i.e. the field `RBM.BoundsCore.decay`, which
  Theorem 2.21 assumes anyway.
* `RBM.Eq548EntryData'`, `RBM.Eq548EntryData.toPrime`, `RBM.flowEq548Sm_of_entryData'` —
  **T241**: the same entrywise package with the field `init` deleted.
* `RBM.thm221NoEL_of_inputs_entries'` — **T241**: the assembly whose (5.48) slot asks for
  `RBM.Eq548EntryData'` and receives the `RBM.BoundsCore X E s` that `RBM.Thm221NoEL.step`
  gets anyway, so that **`init` no longer occurs in the hypothesis table**.
  `RBM.thm221NoEL_of_inputs_entries_of_unprimed` is the compiled certificate that the new
  table is weaker than the old one, and `RBM.thm221Assembly_init_witness` the satisfiability
  witness of the producer.

## What this file does **not** close

The five other named inputs of Steps 1–5 (`RBM.Step1.Hyp`,
`RBM.MomentDuhamelCut.MomentHypCut`, the Step-3 `≺` input, `RBM.Step3.Lemma514`,
`RBM.StepGlue.Eq45Flow`) and, inside the (5.48) item, the three fields of T228 that have no
producer yet (`hmeas`, `hmod`, `hmoment`) are **still hypotheses**, listed as such in the
signature of `RBM.thm221NoEL_of_inputs_entries'`.  They are not hidden behind a bundle that no
object satisfies — see §4 and §7.  The initial bound `hinit` is **no longer among them**
(T241, §5–§7).

## Deviations from the paper

None: this file only composes statements already in the tree.

Bookkeeping for §8 (T245), so that the direction of each change is on the record:

* deleting `RBM.Eq548EntryData.init` and `.meas`, and reading `.modulus` at `∀ᶠ N in atTop`
  instead of `∀ N`, each make the (5.48) package **weaker** — `RBM.Eq548EntryData.toEv`
  compiles, so nothing that satisfied T239's table stops satisfying
  `RBM.thm221NoEL_of_inputs_entriesEv`'s;
* the `∀ᶠ N` reading of the modulus is T244's repair of a field that is **false** as written
  (`RBM.not_entryModulus_of_jSfarSm_ne`); the paper states no such field, so this is an
  internal shape fix and carries no paper-delta of its own — any delta for it belongs to T244;
* `RBM.thm221NoEL_of_inputs_entriesEv` and `RBM.thm221NoEL_of_inputs_cutHyp'` use the
  `RBM.BoundsCore X E s` that `RBM.Thm221NoEL.step` already receives; no slot gains a premise,
  and the conclusion `RBM.Thm221NoEL X κ` is byte-identical.
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

/-! ### 5. `init` is **not** an independent hypothesis: it comes from `BoundsCore` (T241)

`RBM.Eq548EntryData.init` — the left endpoint `J*^{sm}_{s_N,D} ≺ 1` of the (5.48) bootstrap —
is in the paper the value at `u = s_N` of **(2.69) = (2.63)**, and (2.69) at the time `s` is a
*hypothesis of Theorem 2.21 itself*: the field `RBM.BoundsCore.decay`.  T239 found it listed
as an independent sixth datum only because `RBM.thm221NoEL_of_inputs_W` does not pass the
`hB : RBM.BoundsCore X E s` it already has in scope (the tenth argument of
`RBM.Thm221NoEL.step`) down to the (5.48) slot.

This section closes that gap.  Giving the slot an extra `RBM.BoundsCore X E s →` antecedent is
a **free strengthening** of the theorem — the hypothesis becomes weaker, and
`RBM.thm221NoEL_of_inputs_entries_of_unprimed` below is the compiled proof that everything
which satisfied the old table satisfies the new one.

The estimate is the elementary one: (2.69) bounds `|(L-K)_{s,(+,-),a}|` by
`(W ℓ_s η_s)^{-2}(e^{-(‖a₁-a₂‖/ℓ_s)^{1/2}} + W^{-D})`, which is `≤ T_{s,D}(‖a₁-a₂‖)` of (5.27)
as soon as `W ℓ_s η_s ≥ 1` (`inv_sq_mul_decayProf_le_tT`; the scale bound is (2.72), through
`RBM.Step1.eventually_one_le_scale_s`).  Then `RBM.Step2.jStar_le` turns the pointwise bound
`lkFarSm ≤ N^{τ/2} T_{s,D}` into `J*^{sm}_{s_N,D} ≤ N^{τ/2} + 1 ≤ N^τ`, which is exactly what
`≺ 1` asks for.  No smoothing property of `RBM.Step2FarMart.farChi` is used beyond
`lkFarSm ≤ |(L-K)|` (`RBM.Step2FarMart.lkFarSm_le`), so the same proof would serve the sharp
`RBM.Step2FarMart.jSfar`. -/

section Init

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- **(2.69)'s profile is below (5.27)'s tail**:
`(W ℓ_u η_u)^{-2}·(e^{-(d/ℓ_u)^{1/2}} + W^{-D}) ≤ T_{u,D}(d)` once `W ℓ_u η_u ≥ 1`.

The only difference between the two right-hand sides is where the `W^{-D}` sits: (2.69) has it
*inside* the `(W ℓ_u η_u)^{-2}`, (5.27) outside.  The converse direction (with a loss of `W^4`)
is `RBM.Step2.tT_le_decayProf`. -/
theorem inv_sq_mul_decayProf_le_tT {E : ℝ} {N : ℕ} {u D : ℝ} (hA1 : 1 ≤ B.scale E N u)
    (a b : ZMod (B.L N)) :
    (B.scale E N u)⁻¹ ^ 2 * B.decayProf N u D a b
      ≤ Step2.tT B E N D u (zdist (B.L N) (a - b)) := by
  have hW0 : (0 : ℝ) < (B.W N : ℝ) := by exact_mod_cast B.W_pos N
  have hinv : (B.scale E N u)⁻¹ ^ 2 ≤ 1 := by
    rw [inv_pow]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ hA1)
  have hWD : (0 : ℝ) ≤ (B.W N : ℝ) ^ (-D) := Real.rpow_nonneg hW0.le _
  have hexp : (0 : ℝ) ≤
      Real.exp (-√((zdist (B.L N) (a - b) : ℝ) / B.ell N u)) := (Real.exp_pos _).le
  have ht : Step2.tT B E N D u (zdist (B.L N) (a - b))
      = (B.scale E N u)⁻¹ ^ 2 *
          Real.exp (-√((zdist (B.L N) (a - b) : ℝ) / B.ell N u))
        + (B.W N : ℝ) ^ (-D) := by
    simp only [Step2.tT, tailT, Band.scale, inv_pow]
  have hd : B.decayProf N u D a b
      = Real.exp (-√((zdist (B.L N) (a - b) : ℝ) / B.ell N u))
        + (B.W N : ℝ) ^ (-D) := by
    simp only [Band.decayProf, ← Real.sqrt_eq_rpow]
  rw [ht, hd]
  nlinarith [hinv, hWD, hexp]

/-- **`RBM.Eq548EntryData.init` from `RBM.BoundsCore`** (T241).

`jSfarSm ≺ 1` at the left endpoint `u = s_N` is (2.69) at that time, i.e. the field
`RBM.BoundsCore.decay`, plus the scale bound `W ℓ_s η_s ≥ 1` that (2.72) supplies.  So the
initial datum of the (5.48) bootstrap has a **producer**, and is not a hypothesis. -/
theorem stochDom_jSfarSm_init_of_boundsCore (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hc : Cond272 B E s t)
    (hB : BoundsCore X E s) (D : ℝ) (hD : 0 < D) :
    StochDom B.P (fun N (_ : Unit) ω => Step2FarMart.jSfarSm X E D N (s N) ω)
      (fun _ _ _ => (1 : ℝ)) := by
  refine StochDom.of_subset_union (hB.decay D hD) (hB.decay D hD)
    fun τ hτ => ⟨τ / 2, half_pos hτ, ?_⟩
  filter_upwards [Step1.eventually_one_le_scale_s (B := B) (s := s) (t := t) hE hst ht1 hc,
    eventually_le_rpow (2 : ℝ) (half_pos hτ)] with N hA1 hN2
  intro ω hω
  obtain ⟨u0, hbig0⟩ := hω
  have hbig : (N : ℝ) ^ τ < Step2FarMart.jSfarSm X E D N (s N) ω := by simpa using hbig0
  by_contra hno
  simp only [Set.mem_union, badSet, Set.mem_ofPred_eq, not_or, not_exists, not_lt] at hno
  obtain ⟨hno, -⟩ := hno
  have hW0 : (0 : ℝ) < (B.W N : ℝ) := by exact_mod_cast B.W_pos N
  have hτ0 : (0 : ℝ) ≤ (N : ℝ) ^ (τ / 2) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hkey : ∀ a : LoopArg (B.L N) 2,
      Step2FarMart.lkFarSm X E N (s N) ω a
        ≤ (N : ℝ) ^ (τ / 2) *
          tailT (B.W N : ℝ) (B.ell N (s N)) (etaT E (s N)) D
            (zdist (B.L N) (a 0 - a 1)) := by
    intro a
    refine (Step2FarMart.lkFarSm_le X a).trans ?_
    rw [Step2.norm_lk_eq]
    refine (hno (a 0, a 1)).trans ?_
    exact mul_le_mul_of_nonneg_left (inv_sq_mul_decayProf_le_tT hA1 (a 0) (a 1)) hτ0
  have hJ : Step2FarMart.jSfarSm X E D N (s N) ω ≤ (N : ℝ) ^ (τ / 2) + 1 :=
    Step2.jStar_le hW0 hkey
  have hsq : (2 : ℝ) * (N : ℝ) ^ (τ / 2) ≤ (N : ℝ) ^ τ := by
    rw [← UnifDetDom.rpow_half_mul_rpow_half N hτ]
    exact mul_le_mul_of_nonneg_right hN2 hτ0
  linarith

end Init

/-! ### 6. The entrywise package with `init` deleted, and the assembly (T241) -/

section Entries'

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- **`RBM.Eq548EntryData` with the field `init` deleted** — the four entrywise data of (5.48)
that really are open.  The four field types are verbatim those of `RBM.Eq548EntryData`
(`RBM.Eq548EntryData.toPrime` is the forgetful map), and `init` is now produced by
`RBM.stochDom_jSfarSm_init_of_boundsCore` out of `RBM.BoundsCore X E s`. -/
structure Eq548EntryData' (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) : Prop where
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

variable {E : ℝ} {s t : ℕ → ℝ}

/-- Forgetting `init`: the old package is stronger than the new one. -/
theorem Eq548EntryData.toPrime {X : Sample B} (H : Eq548EntryData X E s t) :
    Eq548EntryData' X E s t :=
  ⟨H.near, H.meas, H.modulus, H.moment⟩

/-- **The (5.48) slot from the four open entrywise data, `init` produced from `BoundsCore`.** -/
theorem flowEq548Sm_of_entryData' (X : Sample B) (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hc : Cond272 B E s t)
    (hB : BoundsCore X E s) (H : Eq548EntryData' X E s t) :
    FlowEq548Sm X E s t :=
  flowEq548Sm_of_entries X hst hs0 ht1 H.near H.meas H.modulus H.moment
    (stochDom_jSfarSm_init_of_boundsCore X (t := t) hE hst ht1 hc hB)

end Entries'

section Assembly'

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- **Theorem 2.21 without (2.71), in D13's shape, with `init` removed from the (5.48) slot.**

Verbatim `RBM.thm221NoEL_of_inputs_entries` except that the (5.48) slot asks for
`RBM.Eq548EntryData'` — the same package with the field `init` deleted — and is handed the
`RBM.BoundsCore X E s` that `RBM.Thm221NoEL.step` receives anyway.  The `init` datum is then
produced by `RBM.stochDom_jSfarSm_init_of_boundsCore`, so it **no longer occurs in the
hypothesis table**.

Nothing is weakened: the extra `RBM.BoundsCore X E s →` in front of the slot makes that
hypothesis *weaker* (`RBM.thm221NoEL_of_inputs_entries_of_unprimed` derives the conclusion from
the old table), and the conclusion `RBM.Thm221NoEL X κ` is literally the same as in
`RBM.thm221NoEL_of_inputs_W`. -/
theorem thm221NoEL_of_inputs_entries' (X : Sample B) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
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
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg B E s t c → BoundsCore X E s →
      Eq548EntryData' X E s t) :
    Thm221NoEL X κ where
  step E hE c hc0 s t hs0 hst ht1 hreg hB :=
    boundsCore_step_of_inputs_reg_W X hκ0 hκ1 hE hs0 hst ht1 hc0 hreg hB
      (h1 E hE s t hs0 hst ht1 c hc0 hreg) (Hy E hE s t hs0 hst ht1 c hc0 hreg)
      (hΘ E hE s t hs0 hst ht1 c hc0 hreg) (h514 E hE s t hs0 hst ht1 c hc0 hreg)
      (h45 E hE s t hs0 hst ht1 c hc0 hreg)
      (flowEq548Sm_of_entryData' X (by linarith : |E| < 2) hs0 hst ht1 hreg.toCond272 hB
        (h548e E hE s t hs0 hst ht1 c hc0 hreg hB))

/-- **The new hypothesis table is weaker than the old one** — the compiled certificate that
deleting `init` costs nothing.  Given the six inputs of
`RBM.thm221NoEL_of_inputs_entries` (whose (5.48) slot still carries `init`), the primed
assembly delivers `RBM.Thm221NoEL X κ`: the `RBM.BoundsCore X E s` antecedent is simply
ignored and `RBM.Eq548EntryData.toPrime` drops the extra field. -/
theorem thm221NoEL_of_inputs_entries_of_unprimed (X : Sample B) {κ : ℝ} (hκ0 : 0 < κ)
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
    Thm221NoEL X κ :=
  thm221NoEL_of_inputs_entries' X hκ0 hκ1 h1 Hy hΘ h514 h45
    fun E hE s t hs0 hst ht1 c hc0 hreg _ =>
      (h548e E hE s t hs0 hst ht1 c hc0 hreg).toPrime

end Assembly'

/-! ### 7. Satisfiability of the `init` producer (T241)

The producer's own hypotheses have to be jointly satisfiable, or `init` has been "removed" only
by being made unreachable.  They are: `|E| < 2`, `s ≤ t`, `t < 1`, `RBM.Cond272` and
`RBM.BoundsCore X E s`.  On T202's explicit band model at `E = 0` and the start `s ≡ 0` of the
grid of p. 24 — the very step `RBM.thm221Assembly_hyp_consistent` certifies — all five hold at
once, and the conclusion `jSfarSm ≺ 1` follows.  `RBM.gridT_zero` is what identifies the
grid's `k = 0` time with the `s ≡ 0` at which `RBM.boundsCore_gauss_witness` lives.

Together with `RBM.thm221Assembly_far_critical` (`1 ≤ jSfarSm` for **every** `ω`, so the
conclusion is not something the degenerate `ω = 0` meets for free) this says the producer is
both usable and non-trivial. -/

section SatisfiableInit

/-- **The `init` producer fires on T202's explicit model** (T241): at `E = 0`, on the first
step `s ≡ 0 → t = u_1` of the grid of p. 24, all five hypotheses of
`RBM.stochDom_jSfarSm_init_of_boundsCore` hold simultaneously and the deleted field `init` is
*obtained*.  So `RBM.Eq548EntryData'` is `RBM.Eq548EntryData` with a field that is genuinely
derivable, not with a field that was quietly dropped. -/
theorem thm221Assembly_init_witness {τ : ℝ} (hτ0 : 0 < τ) :
    ∃ τ' : ℝ, 0 < τ' ∧ ∃ c : ℝ, 0 < c ∧
      ∀ t : ℕ → ℝ, (∀ N, 0 ≤ t N) →
        (∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-1 + τ) ≤ 1 - t N) →
        ∃ v : ℕ → ℝ, (∀ N, (0 : ℝ) ≤ v N) ∧ (∀ N, v N < 1) ∧
          Cond272Reg (Gauss.band Gauss.Dims.exampleGrow) 0 (fun _ => 0) v c ∧
          BoundsCore (Gauss.sample Gauss.Dims.exampleGrow) 0 (fun _ => 0) ∧
          ∀ D : ℝ, 0 < D → StochDom (Gauss.band Gauss.Dims.exampleGrow).P
            (fun N (_ : Unit) ω =>
              Step2FarMart.jSfarSm (Gauss.sample Gauss.Dims.exampleGrow) 0 D N 0 ω)
            (fun _ _ _ => (1 : ℝ)) := by
  obtain ⟨τ', hτ'0, c, hc0, n₀, hgrid⟩ :=
    cond272Reg_grid_step_domain (Gauss.band Gauss.Dims.exampleGrow)
      (κ := 1) (τ := τ) one_pos hτ0
  refine ⟨τ', hτ'0, c, hc0, fun t ht0 ht => ?_⟩
  obtain ⟨-, hstep⟩ := hgrid 0 (by norm_num) t ht0 ht
  obtain ⟨-, hmono, h1lt, hreg⟩ := hstep 0
  have hz : ∀ N : ℕ,
      gridT ((Gauss.band Gauss.Dims.exampleGrow).W N) τ' (t N) 0 = 0 :=
    fun N => gridT_zero (ht0 N)
  have hzf : (fun N => gridT ((Gauss.band Gauss.Dims.exampleGrow).W N) τ' (t N) 0)
      = (fun _ : ℕ => (0 : ℝ)) := funext hz
  rw [hzf] at hreg
  have hmono' : ∀ N : ℕ,
      (0 : ℝ) ≤ gridT ((Gauss.band Gauss.Dims.exampleGrow).W N) τ' (t N) 1 := by
    intro N
    have := hmono N
    rwa [hz N] at this
  refine ⟨fun N => gridT ((Gauss.band Gauss.Dims.exampleGrow).W N) τ' (t N) 1,
    hmono', h1lt, hreg, boundsCore_gauss_witness.1, fun D hD => ?_⟩
  exact stochDom_jSfarSm_init_of_boundsCore (Gauss.sample Gauss.Dims.exampleGrow)
    (by norm_num) hmono' h1lt hreg.toCond272 boundsCore_gauss_witness.1 D hD

end SatisfiableInit


/-! ### 8. The (5.48) package at the repaired shapes (T245)

T244 proved that `RBM.Eq548EntryData.modulus` — and therefore the same field of
`RBM.Eq548EntryData'` — is **false as written**: its right-hand side is
`N ^ 1 * |v - w| ^ (1/2)`, which vanishes identically at `N = 0`
(`RBM.modulus_rhs_eq_zero_at_zero`), so at `N = 0` the field is not a modulus of continuity but
the *equality constraint* that `v ↦ ‖(L-K)_v‖ / T_{v,D}` be constant on the whole of
`[s_0, t_0]`, for **every** `ω` and every label pair.  `RBM.not_entryModulus_of_jSfarSm_ne` and
`RBM.not_entryModulus_of_ratio_ne` are the compiled refutations.  T244's repair is
`RBM.EntryModulusEv`, the same body read at `∀ᶠ N in atTop`, which the `N = 0` argument cannot
touch (`RBM.entryModulusEv_of_forall_pos` below), and `RBM.MomentDuhamelCut.satCutHypEv`
together with `RBM.MomentDuhamelCut.sat_modulus_not_forall` is T232's compiled proof that the
`∀ᶠ N` reading is *strictly* weaker at the flow's own exponents `Kmod = 1`, `γ = 1/2`.

`RBM.Eq548EntryDataEv` is therefore `RBM.Eq548EntryData` with

* `init` **deleted** (T241: `RBM.stochDom_jSfarSm_init_of_boundsCore` produces it from
  `RBM.BoundsCore X E s`, which `RBM.Thm221NoEL.step` receives anyway);
* `meas` **deleted** (T244: `RBM.aestronglyMeasurable_jSfarSm` proves it with **no**
  hypotheses, for every `X` and every sample point);
* `modulus` **weakened** from the refuted `∀ N` shape to `RBM.EntryModulusEv`.

All three changes make the package *weaker*, so `RBM.Eq548EntryData.toEv` compiles and the
merged table cannot be harder to satisfy than T239's.  Only `near` (→ `Step2Near47`/T207, and
`RBM.Eq548EntryDataEv.of_sharp` records that route) and `moment` (→ T230/T210) are left. -/

section EntriesEv

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E D : ℝ} {s t : ℕ → ℝ}

/-- **T244's `N = 0` refutation cannot reach the `∀ᶠ N` field.**  It suffices to have the
entrywise modulus for `N ≥ 1`; the instance at `N = 0`, which
`RBM.not_entryModulus_of_jSfarSm_ne` refutes, is never asked for. -/
theorem entryModulusEv_of_forall_pos (X : Sample B)
    (h : ∀ N : ℕ, 1 ≤ N → ∀ ω : Ω, ∀ v ∈ Set.Icc (s N) (t N), ∀ w ∈ Set.Icc (s N) (t N),
      ∀ x : LoopArg (B.L N) 2,
        15 / 8 * |(zdist (B.L N) (x 0 - x 1) : ℝ) / (6 * ellStar (B.W N : ℝ) (B.ell N v))
              - (zdist (B.L N) (x 0 - x 1) : ℝ) / (6 * ellStar (B.W N : ℝ) (B.ell N w))|
            * |‖Step2.lk X E N v ω x‖ / tailT (B.W N : ℝ) (B.ell N v) (etaT E v) D
                (zdist (B.L N) (x 0 - x 1))|
          + |‖Step2.lk X E N v ω x‖ / tailT (B.W N : ℝ) (B.ell N v) (etaT E v) D
                (zdist (B.L N) (x 0 - x 1))
              - ‖Step2.lk X E N w ω x‖ / tailT (B.W N : ℝ) (B.ell N w) (etaT E w) D
                (zdist (B.L N) (x 0 - x 1))|
            ≤ (N : ℝ) ^ (1 : ℝ) * |v - w| ^ ((1 : ℝ) / 2)) :
    EntryModulusEv X E s t D :=
  Filter.eventually_atTop.2 ⟨1, h⟩

/-- **The entrywise data of (5.48), at the shapes that survive the audit** (T245).

Two fields, both genuinely open:

* `near` — the sharp near half (5.47), verbatim the field of `RBM.Eq548EntryData`
  (→ `Step2Near47`/T207; `RBM.Eq548EntryDataEv.of_sharp` builds it from
  `RBM.Step2Near47.MomentHypCutSharp`);
* `moment` — the truncated moment bound on the net, verbatim the field of
  `RBM.Eq548EntryData` (→ T230/T210).

and one field at T244's repaired shape:

* `modulus` — `RBM.EntryModulusEv`, i.e. the `∀ N` modulus of `RBM.Eq548EntryData.modulus`
  read at `∀ᶠ N in atTop`.

`meas` and `init` are gone: they are theorems (`RBM.aestronglyMeasurable_jSfarSm`,
`RBM.stochDom_jSfarSm_init_of_boundsCore`). -/
structure Eq548EntryDataEv (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) : Prop where
  near : ∀ D : ℝ, 0 < D → StochDom B.P
    (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
      X.lkErr E N p.1 ω (pmLoop p.2.1 p.2.2))
    (fun N p _ => (etaT E (s N) / etaT E p.1) ^ 2 *
      tailT (B.W N : ℝ) (B.ell N p.1) (etaT E p.1) D (zdist (B.L N) (p.2.1 - p.2.2)))
  modulus : ∀ D : ℝ, 0 < D → EntryModulusEv X E s t D
  moment : ∀ D : ℝ, 0 < D → ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ ε > (0 : ℝ), ∀ p : ℕ, ∃ C > (0 : ℝ),
    ∀ᶠ N : ℕ in atTop,
    ∀ ws ∈ MomentDuhamelCut.netFinset s t (fun N => ((N : ℝ) + 1) ^ (2 : ℝ)) N,
      ∫ ω, |MomentDuhamelCut.cutTrunc ((N : ℝ) ^ (2 * δ) * 1)
            (Step2FarMart.jSfarSm X E D N ws ω)| ^ (2 * p) ∂B.P
        ≤ C * ((N : ℝ) ^ (ε * p) * (1 : ℝ) ^ (2 * p))

/-- **The old package is stronger than the new one** — the field-by-field certificate that
deleting `init` and `meas` and weakening `modulus` to its `∀ᶠ N` reading costs nothing. -/
theorem Eq548EntryData.toEv {X : Sample B} (H : Eq548EntryData X E s t) :
    Eq548EntryDataEv X E s t :=
  ⟨H.near, fun D hD => entryModulusEv_of_entryModulus X (H.modulus D hD), H.moment⟩

/-- Same, from T241's four-field package. -/
theorem Eq548EntryData'.toEv {X : Sample B} (H : Eq548EntryData' X E s t) :
    Eq548EntryDataEv X E s t :=
  ⟨H.near, fun D hD => entryModulusEv_of_entryModulus X (H.modulus D hD), H.moment⟩

/-- **`RBM.Eq548EntryDataEv` from T207's sharp (5.47)** (T244's `RBM.near_of_sharp`).  Kept as
a *constructor* rather than as the shape of the `near` field: `RBM.near_of_sharp` shows
`RBM.Step2Near47.MomentHypCutSharp` is at least as strong as the field, so putting it into the
structure would **strengthen** the request and `Eq548EntryData.toEv` would no longer compile. -/
theorem Eq548EntryDataEv.of_sharp {X : Sample B} (hE : |E| < 2) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1)
    (hnear : ∀ D : ℝ, 0 < D → Step2Near47.MomentHypCutSharp X E s t D)
    (hmod : ∀ D : ℝ, 0 < D → EntryModulusEv X E s t D)
    (hmoment : ∀ D : ℝ, 0 < D → ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ ε > (0 : ℝ), ∀ p : ℕ,
      ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      ∀ ws ∈ MomentDuhamelCut.netFinset s t (fun N => ((N : ℝ) + 1) ^ (2 : ℝ)) N,
        ∫ ω, |MomentDuhamelCut.cutTrunc ((N : ℝ) ^ (2 * δ) * 1)
              (Step2FarMart.jSfarSm X E D N ws ω)| ^ (2 * p) ∂B.P
          ≤ C * ((N : ℝ) ^ (ε * p) * (1 : ℝ) ^ (2 * p))) :
    Eq548EntryDataEv X E s t :=
  ⟨near_of_sharp X hnear hE hst ht1, hmod, hmoment⟩

/-- **The (5.48) slot from `RBM.Eq548EntryDataEv`** — `meas` discharged by T244's
`RBM.aestronglyMeasurable_jSfarSm`, `init` by T241's
`RBM.stochDom_jSfarSm_init_of_boundsCore`, and the bootstrap routed through T232's asymptotic
interface `RBM.MomentDuhamelCut.CutHypEv` (T244's `RBM.stochDom_jSfarSm_of_entriesEv`) so that
the refuted `∀ N` modulus never appears. -/
theorem flowEq548Sm_of_entryDataEv (X : Sample B) (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hc : Cond272 B E s t)
    (hB : BoundsCore X E s) (H : Eq548EntryDataEv X E s t) :
    FlowEq548Sm X E s t :=
  flowEq548Sm_of_nearChi X ht1
    (Step2FarMart.flowEq548W_of_jSfarSm X H.near fun D hD =>
      stochDom_jSfarSm_of_entriesEv X hst hs0 ht1 (H.modulus D hD) (H.moment D hD)
        (stochDom_jSfarSm_init_of_boundsCore X (t := t) hE hst ht1 hc hB D hD))

end EntriesEv

section AssemblyEv

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- **Theorem 2.21 without (2.71), with the whole of `meas`, `init` and the refuted `∀ N`
modulus out of the (5.48) slot** (T245).

Verbatim `RBM.thm221NoEL_of_inputs_entries` except that the last slot asks for
`RBM.Eq548EntryDataEv` — three fields instead of five, one of them at T244's repaired
`∀ᶠ N` shape.  No extra premise is needed on the slot: `RBM.BoundsCore X E s`, which the `init`
producer consumes, is an argument of `RBM.Thm221NoEL.step` itself.

`RBM.thm221NoEL_of_inputs_entriesEv_of_unprimed` is the compiled certificate that this is a free
strengthening. -/
theorem thm221NoEL_of_inputs_entriesEv (X : Sample B) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
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
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg B E s t c → Eq548EntryDataEv X E s t) :
    Thm221NoEL X κ where
  step E hE c hc0 s t hs0 hst ht1 hreg hB :=
    boundsCore_step_of_inputs_reg_W X hκ0 hκ1 hE hs0 hst ht1 hc0 hreg hB
      (h1 E hE s t hs0 hst ht1 c hc0 hreg) (Hy E hE s t hs0 hst ht1 c hc0 hreg)
      (hΘ E hE s t hs0 hst ht1 c hc0 hreg) (h514 E hE s t hs0 hst ht1 c hc0 hreg)
      (h45 E hE s t hs0 hst ht1 c hc0 hreg)
      (flowEq548Sm_of_entryDataEv X (by linarith : |E| < 2) hs0 hst ht1 hreg.toCond272 hB
        (h548e E hE s t hs0 hst ht1 c hc0 hreg))

/-- **The new (5.48) slot is weaker than T239's** — everything that satisfied
`RBM.thm221NoEL_of_inputs_entries`'s table satisfies this one, by
`RBM.Eq548EntryData.toEv`. -/
theorem thm221NoEL_of_inputs_entriesEv_of_unprimed (X : Sample B) {κ : ℝ} (hκ0 : 0 < κ)
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
    Thm221NoEL X κ :=
  thm221NoEL_of_inputs_entriesEv X hκ0 hκ1 h1 Hy hΘ h514 h45
    fun E hE s t hs0 hst ht1 c hc0 hreg => (h548e E hE s t hs0 hst ht1 c hc0 hreg).toEv

/-- **T241's `hinit` slot removed from the `CutHyp` route too** (the mechanical half of T245).
Verbatim `RBM.thm221NoEL_of_inputs_cutHyp` **minus** its last hypothesis: the same
`RBM.stochDom_jSfarSm_init_of_boundsCore` supplies it from the `RBM.BoundsCore X E s` that
`RBM.Thm221NoEL.step` already carries.  Strictly fewer hypotheses, identical conclusion. -/
theorem thm221NoEL_of_inputs_cutHyp' (X : Sample B) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
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
        (fun _ => 1)) :
    Thm221NoEL X κ where
  step E hE c hc0 s t hs0 hst ht1 hreg hB :=
    boundsCore_step_of_inputs_reg_W X hκ0 hκ1 hE hs0 hst ht1 hc0 hreg hB
      (h1 E hE s t hs0 hst ht1 c hc0 hreg) (Hy E hE s t hs0 hst ht1 c hc0 hreg)
      (hΘ E hE s t hs0 hst ht1 c hc0 hreg) (h514 E hE s t hs0 hst ht1 c hc0 hreg)
      (h45 E hE s t hs0 hst ht1 c hc0 hreg)
      (flowEq548Sm_of_cutHyp X ht1 (hnear E hE s t hs0 hst ht1 c hc0 hreg)
        (hcut E hE s t hs0 hst ht1 c hc0 hreg)
        (stochDom_jSfarSm_init_of_boundsCore X (t := t) (by linarith : |E| < 2) hst ht1
          hreg.toCond272 hB))

/-- **The `CutHyp` route's new table is weaker than T239's** — the old `hinit` input is simply
ignored. -/
theorem thm221NoEL_of_inputs_cutHyp'_of_unprimed (X : Sample B) {κ : ℝ} (hκ0 : 0 < κ)
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
    (_hinit : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg B E s t c → ∀ D : ℝ, 0 < D →
      StochDom B.P (fun N (_ : Unit) ω => Step2FarMart.jSfarSm X E D N (s N) ω)
        (fun _ _ _ => (1 : ℝ))) :
    Thm221NoEL X κ :=
  thm221NoEL_of_inputs_cutHyp' X hκ0 hκ1 h1 Hy hΘ h514 h45 hnear hcut

/-- **The step, with the (5.48) item built from `RBM.Eq548EntryDataEv`.**  Verbatim
`RBM.boundsCore_step_of_inputs_reg_W` except in the last slot. -/
theorem boundsCore_step_of_inputs_entriesEv (X : Sample B) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    {E : ℝ} {s t : ℕ → ℝ} (hEκ : |E| ≤ 2 - κ) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c) (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore X E s) (h1 : Step1.Hyp X E s t)
    (Hy : ∀ D : ℝ, 60 ≤ D → MomentDuhamelCut.MomentHypCut X E s t D)
    (hΘ : StochDom B.P (Step3.flowXiLK X E s t 2)
      (fun N (_ : TimeIcc s t N) (_ : Ω) => Step3.flowAs B E s N ^ ((1 : ℝ) / 2)))
    (h514 : ∀ n, 2 ≤ n → Step3.Lemma514 B.P (Step3.flowXiLK X E s t) (Step3.flowXiL X E s t)
      (Step3.flowA B E s t) n)
    (h45 : StepGlue.Eq45Flow X E s t) (H : Eq548EntryDataEv X E s t) :
    BoundsCore X E t :=
  boundsCore_step_of_inputs_reg_W X hκ0 hκ1 hEκ hs0 hst ht1 hc0 hreg hB h1 Hy hΘ h514 h45
    (flowEq548Sm_of_entryDataEv X (lt_of_le_of_lt hEκ (by linarith)) hs0 hst ht1
      hreg.toCond272 hB H)

/-- **The conclusion is byte-identical.**  The step built here and
`RBM.boundsCore_step_of_inputs_reg_W`'s land at the *same* `RBM.BoundsCore X E t`: the
substitution happened strictly in hypothesis positions, and what went in is a theorem
*producing* the old hypothesis. -/
theorem boundsCore_step_of_inputs_entriesEv_unchanged (X : Sample B) {κ : ℝ} (hκ0 : 0 < κ)
    (hκ1 : κ ≤ 1) {E : ℝ} {s t : ℕ → ℝ} (hEκ : |E| ≤ 2 - κ) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c)
    (hreg : Cond272Reg B E s t c) (hB : BoundsCore X E s) (h1 : Step1.Hyp X E s t)
    (Hy : ∀ D : ℝ, 60 ≤ D → MomentDuhamelCut.MomentHypCut X E s t D)
    (hΘ : StochDom B.P (Step3.flowXiLK X E s t 2)
      (fun N (_ : TimeIcc s t N) (_ : Ω) => Step3.flowAs B E s N ^ ((1 : ℝ) / 2)))
    (h514 : ∀ n, 2 ≤ n → Step3.Lemma514 B.P (Step3.flowXiLK X E s t) (Step3.flowXiL X E s t)
      (Step3.flowA B E s t) n)
    (h45 : StepGlue.Eq45Flow X E s t) (H : Eq548EntryDataEv X E s t) :
    boundsCore_step_of_inputs_entriesEv X hκ0 hκ1 hEκ hs0 hst ht1 hc0 hreg hB h1 Hy hΘ h514
        h45 H =
      boundsCore_step_of_inputs_reg_W X hκ0 hκ1 hEκ hs0 hst ht1 hc0 hreg hB h1 Hy hΘ h514 h45
        (flowEq548Sm_of_entryDataEv X (lt_of_le_of_lt hEκ (by linarith)) hs0 hst ht1
          hreg.toCond272 hB H) :=
  rfl

end AssemblyEv

/-! ### 9. T251: the entrywise modulus of (5.48) on a high-probability event

T249 proved (`RBM.not_entryModulusEv_swapSample_of_far`) that `RBM.EntryModulusEv` — the
`modulus` field of `RBM.Eq548EntryDataEv` — is **false** on a window whose left endpoint is
`0`, for the plain reason that it is a *deterministic* inequality quantified over **every**
sample point while the Hölder constant of `u ↦ G_u` along `H_u = √u X` is `O(‖X‖/√s)` and
`‖X‖` is unbounded.  This section is the repair on the `ω` side: the field is asked only for
`ω ∈ Good N`, with `Good` of high probability.  (The repair on the *time* side — the window's
left endpoint `s_N ≥ N^{-C}` — is `RBM.WindowLeft` in `Flow/Step345Producer.lean`; T249's
`⚠` is that neither half works without the other.)

Nothing downstream is reproved.  `RBM.MomentDuhamelCut.CutHypEvOn` (T249丙) transports to the
unrestricted `RBM.MomentDuhamelCut.CutHypEv` for the *restricted* functional
`RBM.MomentDuhamelCut.onEvent J Good`, which is `0` off `Good N`, and
`RBM.MomentDuhamelCut.stochDom_of_cutHypEvOn` pays the exceptional set with one extra `N^{-1}`
in the union bound.  So the only change here is one extra `intro` after the `filter_upwards`
of `RBM.cutHypEv_jSfarSm_of_entries`.

`RBM.Eq548EntryDataEv.toEvOn` and `RBM.Eq548EntryDataEv.toEvOn'` are the compiled certificates
that the event-restricted package is **weaker** (`Good = Set.univ` recovers the old one), so
the new table cannot be harder to satisfy than T245's. -/

section EntriesEvOn

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E D : ℝ} {s t : ℕ → ℝ}
variable {Good : ℕ → Set Ω}

/-- **`RBM.EntryModulusEv` with the deterministic inequality asked only on `Good N`.**  The
body is byte for byte `RBM.EntryModulusEv`'s; the single change is `∀ ω : Ω` ⤳ `∀ ω ∈ Good N`.

This is the shape the satisfiability discipline demands of a deterministic estimate on a
random model, and T249's `RBM.not_entryModulusEv_swapSample_of_far` is the proof that the
unrestricted shape is not merely impolite but false. -/
def EntryModulusEvOn (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) (D : ℝ) (Good : ℕ → Set Ω) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∀ ω ∈ Good N, ∀ v ∈ Set.Icc (s N) (t N), ∀ w ∈ Set.Icc (s N) (t N),
    ∀ x : LoopArg (B.L N) 2,
      15 / 8 * |(zdist (B.L N) (x 0 - x 1) : ℝ) / (6 * ellStar (B.W N : ℝ) (B.ell N v))
            - (zdist (B.L N) (x 0 - x 1) : ℝ) / (6 * ellStar (B.W N : ℝ) (B.ell N w))|
          * |‖Step2.lk X E N v ω x‖ / tailT (B.W N : ℝ) (B.ell N v) (etaT E v) D
              (zdist (B.L N) (x 0 - x 1))|
        + |‖Step2.lk X E N v ω x‖ / tailT (B.W N : ℝ) (B.ell N v) (etaT E v) D
              (zdist (B.L N) (x 0 - x 1))
            - ‖Step2.lk X E N w ω x‖ / tailT (B.W N : ℝ) (B.ell N w) (etaT E w) D
              (zdist (B.L N) (x 0 - x 1))|
          ≤ (N : ℝ) ^ (1 : ℝ) * |v - w| ^ ((1 : ℝ) / 2)

/-- The restriction really is a weakening: an unrestricted modulus is one on every event. -/
theorem entryModulusEvOn_of_entryModulusEv (X : Sample B) (h : EntryModulusEv X E s t D)
    (Good : ℕ → Set Ω) : EntryModulusEvOn X E s t D Good := by
  filter_upwards [h] with N hN ω _ v hv w hw x using hN ω v hv w hw x

/-- At `Good = Set.univ` the two shapes agree, so nothing was lost in the other direction
either. -/
theorem entryModulusEv_of_entryModulusEvOn_univ (X : Sample B)
    (h : EntryModulusEvOn X E s t D (fun _ => Set.univ)) : EntryModulusEv X E s t D := by
  filter_upwards [h] with N hN ω v hv w hw x using hN ω (Set.mem_univ ω) v hv w hw x

/-- **`RBM.MomentDuhamelCut.CutHypEvOn` for `J*^{sm}_{u,D}`.**  Field for field
`RBM.cutHypEv_jSfarSm_of_entries`, with `good_meas` added and one extra `intro` in `modulus`:
the entrywise estimate is consumed on `Good N` exactly as it was consumed on all of `Ω`. -/
noncomputable def cutHypEvOn_jSfarSm_of_entries (X : Sample B)
    (hst : ∀ N, s N ≤ t N) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    (hgm : ∀ N, MeasurableSet (Good N))
    (hmod : EntryModulusEvOn X E s t D Good)
    (hmoment : ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ ε > (0 : ℝ), ∀ p : ℕ, ∃ C > (0 : ℝ),
      ∀ᶠ N : ℕ in atTop,
      ∀ ws ∈ MomentDuhamelCut.netFinset s t (fun N => ((N : ℝ) + 1) ^ (2 : ℝ)) N,
        ∫ ω, |MomentDuhamelCut.cutTrunc ((N : ℝ) ^ (2 * δ) * 1)
              (Step2FarMart.jSfarSm X E D N ws ω)| ^ (2 * p) ∂B.P
          ≤ C * ((N : ℝ) ^ (ε * p) * (1 : ℝ) ^ (2 * p))) :
    MomentDuhamelCut.CutHypEvOn B.P (fun N u ω => Step2FarMart.jSfarSm X E D N u ω) s t
      (fun _ => 1) Good where
  window := hst
  δ₀ := 1
  δ₀_pos := one_pos
  Θ_pos := fun _ => one_pos
  J_nonneg := fun _ _ _ => Step2FarMart.jSfarSm_nonneg X
  meas := fun N u => (measurable_jSfarSm X E D N u).aestronglyMeasurable
  good_meas := hgm
  mesh := fun N => ((N : ℝ) + 1) ^ (2 : ℝ)
  mesh_pos := fun N => Real.rpow_pos_of_pos (by positivity) _
  Kmod := 1
  γ := 1 / 2
  γ_pos := by norm_num
  modulus := by
    filter_upwards [hmod] with N hN ω hω v hv w hw
    exact Step2FarMart.abs_jSfarSm_sub_le X fun x =>
      (Step2FarMart.abs_lkFarSm_ratio_sub_le X x).trans (hN ω hω v hv w hw x)
  mesh_fine := Filter.Eventually.of_forall Step2FarMart.mesh_fine_one_at_sq
  Ccard := 3
  card_le := Step2FarMart.card_le_one_at_sq hs0 ht1
  moment := hmoment

/-- **`J*^{sm}_{u,D} ≺ 1` from the event-restricted entrywise data** — verbatim
`RBM.stochDom_jSfarSm_of_entriesEv` with `RBM.MomentDuhamelCut.stochDom_of_cutHypEvOn` in place
of `RBM.MomentDuhamelCut.stochDom_of_cutHypEv`.  The conclusion is **unchanged**: it is a
`StochDom` for the honest, unrestricted functional; the event is paid for inside. -/
theorem stochDom_jSfarSm_of_entriesEvOn (X : Sample B)
    (hst : ∀ N, s N ≤ t N) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    (hgm : ∀ N, MeasurableSet (Good N)) (hgood : HighProb B.P Good)
    (hmod : EntryModulusEvOn X E s t D Good)
    (hmoment : ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ ε > (0 : ℝ), ∀ p : ℕ, ∃ C > (0 : ℝ),
      ∀ᶠ N : ℕ in atTop,
      ∀ ws ∈ MomentDuhamelCut.netFinset s t (fun N => ((N : ℝ) + 1) ^ (2 : ℝ)) N,
        ∫ ω, |MomentDuhamelCut.cutTrunc ((N : ℝ) ^ (2 * δ) * 1)
              (Step2FarMart.jSfarSm X E D N ws ω)| ^ (2 * p) ∂B.P
          ≤ C * ((N : ℝ) ^ (ε * p) * (1 : ℝ) ^ (2 * p)))
    (hinit : StochDom B.P (fun N (_ : Unit) ω => Step2FarMart.jSfarSm X E D N (s N) ω)
      (fun _ _ _ => (1 : ℝ))) :
    StochDom B.P (fun N (u : TimeIcc s t N) ω => Step2FarMart.jSfarSm X E D N (u : ℝ) ω)
      (fun _ _ _ => (1 : ℝ)) :=
  letI := B.isProbabilityMeasure
  MomentDuhamelCut.stochDom_of_cutHypEvOn
    (cutHypEvOn_jSfarSm_of_entries X hst hs0 ht1 hgm hmod hmoment) hgood
    (Filter.Eventually.of_forall fun _ => le_rfl) hinit

/-- **The entrywise data of (5.48) with the modulus restricted to `Good`** — `near` and
`moment` are byte for byte the fields of `RBM.Eq548EntryDataEv`; only `modulus` changed. -/
structure Eq548EntryDataEvOn (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) (Good : ℕ → Set Ω) :
    Prop where
  near : ∀ D : ℝ, 0 < D → StochDom B.P
    (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
      X.lkErr E N p.1 ω (pmLoop p.2.1 p.2.2))
    (fun N p _ => (etaT E (s N) / etaT E p.1) ^ 2 *
      tailT (B.W N : ℝ) (B.ell N p.1) (etaT E p.1) D (zdist (B.L N) (p.2.1 - p.2.2)))
  modulus : ∀ D : ℝ, 0 < D → EntryModulusEvOn X E s t D Good
  moment : ∀ D : ℝ, 0 < D → ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ ε > (0 : ℝ), ∀ p : ℕ, ∃ C > (0 : ℝ),
    ∀ᶠ N : ℕ in atTop,
    ∀ ws ∈ MomentDuhamelCut.netFinset s t (fun N => ((N : ℝ) + 1) ^ (2 : ℝ)) N,
      ∫ ω, |MomentDuhamelCut.cutTrunc ((N : ℝ) ^ (2 * δ) * 1)
            (Step2FarMart.jSfarSm X E D N ws ω)| ^ (2 * p) ∂B.P
        ≤ C * ((N : ℝ) ^ (ε * p) * (1 : ℝ) ^ (2 * p))

/-- **The (5.48) slot at the shape the satisfiability discipline allows**: the event is
existentially quantified together with its measurability and its high probability, so the slot
is a `Prop` about `X, E, s, t` alone and can sit in the merged table where
`RBM.Eq548EntryDataEv` sat. -/
def Eq548EntryDataEvOn' (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) : Prop :=
  ∃ Good : ℕ → Set Ω, (∀ N, MeasurableSet (Good N)) ∧ HighProb B.P Good ∧
    Eq548EntryDataEvOn X E s t Good

/-- `Ω` itself is of high probability. -/
theorem highProb_univ (P : Measure Ω) : HighProb P (fun _ : ℕ => (Set.univ : Set Ω)) := by
  intro D _
  filter_upwards with N
  simp

/-- **A high-probability event is eventually nonempty** — on a probability space, `HighProb`
forces `P (Good N) > 0` for large `N`.  This is the anti-vacuity certificate the slot needs:
`RBM.EntryModulusEvOn` at `Good = ∅` would be trivially true, and it is `HighProb` in
`RBM.Eq548EntryDataEvOn'` that rules that out. -/
theorem eventually_nonempty_of_highProb {P : Measure Ω} [IsProbabilityMeasure P]
    {Good : ℕ → Set Ω} (h : HighProb P Good) : ∀ᶠ N : ℕ in atTop, (Good N).Nonempty := by
  filter_upwards [h 1 one_pos, Filter.eventually_ge_atTop 2] with N hN hN2
  rw [Set.nonempty_iff_ne_empty]
  intro he
  rw [he, Set.compl_empty, measure_univ] at hN
  have hN2' : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
  have hx : ((N : ℝ)) ^ (-(1 : ℝ)) ≤ 1 / 2 := by
    rw [Real.rpow_neg_one]
    rw [inv_le_iff_one_le_mul₀ (by linarith)]
    linarith
  have : ENNReal.ofReal (((N : ℝ)) ^ (-(1 : ℝ))) ≤ ENNReal.ofReal (1 / 2) :=
    ENNReal.ofReal_le_ofReal hx
  have hhalf : ENNReal.ofReal ((1 : ℝ) / 2) < 1 := ENNReal.ofReal_lt_one.2 (by norm_num)
  exact absurd (lt_of_le_of_lt (hN.trans this) hhalf) (lt_irrefl 1)

/-- **The old package is stronger than the new one, at every event** — the field-by-field
certificate that restricting `modulus` to `Good` costs nothing. -/
theorem Eq548EntryDataEv.toEvOn {X : Sample B} (H : Eq548EntryDataEv X E s t)
    (Good : ℕ → Set Ω) : Eq548EntryDataEvOn X E s t Good :=
  ⟨H.near, fun D hD => entryModulusEvOn_of_entryModulusEv X (H.modulus D hD) Good, H.moment⟩

/-- **The old package is stronger than the slot** — take `Good = Set.univ`. -/
theorem Eq548EntryDataEv.toEvOn' {X : Sample B} (H : Eq548EntryDataEv X E s t) :
    Eq548EntryDataEvOn' X E s t :=
  ⟨fun _ => Set.univ, fun _ => MeasurableSet.univ, highProb_univ B.P, H.toEvOn _⟩

/-- **The slot is not vacuous**: at `Good = Set.univ` it is exactly `RBM.Eq548EntryDataEv`, so
every witness of the old table is a witness of the new one and conversely at that event. -/
theorem Eq548EntryDataEvOn.toEv_univ {X : Sample B}
    (H : Eq548EntryDataEvOn X E s t (fun _ => Set.univ)) : Eq548EntryDataEv X E s t :=
  ⟨H.near, fun D hD => entryModulusEv_of_entryModulusEvOn_univ X (H.modulus D hD), H.moment⟩

/-- **The (5.48) slot from the event-restricted entrywise data** — verbatim
`RBM.flowEq548Sm_of_entryDataEv` with `RBM.stochDom_jSfarSm_of_entriesEvOn` in place of
`RBM.stochDom_jSfarSm_of_entriesEv`.  `init` is still T241's
`RBM.stochDom_jSfarSm_init_of_boundsCore` and `meas` still T244's theorem. -/
theorem flowEq548Sm_of_entryDataEvOn (X : Sample B) (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hc : Cond272 B E s t)
    (hB : BoundsCore X E s) (H : Eq548EntryDataEvOn' X E s t) :
    FlowEq548Sm X E s t := by
  obtain ⟨Good, hgm, hgood, H⟩ := H
  exact flowEq548Sm_of_nearChi X ht1
    (Step2FarMart.flowEq548W_of_jSfarSm X H.near fun D hD =>
      stochDom_jSfarSm_of_entriesEvOn X hst hs0 ht1 hgm hgood (H.modulus D hD) (H.moment D hD)
        (stochDom_jSfarSm_init_of_boundsCore X (t := t) hE hst ht1 hc hB D hD))

end EntriesEvOn


/-! ### 10. T261: the entrywise modulus of (5.48) with its exponents as parameters

T258 proved two things about the `modulus` field of §9:

* `RBM.not_entryModulusEvKOn_one_half_bandGrow` — **`RBM.EntryModulusEvOn` as written in §9 is
  false** on the concrete model `RBM.bandGrow`, with `2 ≤ D` its only premise.  The hard-coded
  right-hand side `(N : ℝ)^1 * |v - w|^{1/2}` is the culprit: its pair `(K_mod, γ) = (1, 1/2)`
  sits exactly on the boundary `K_mod = 2γ` of T258's refuted range.
* `RBM.not_cutHypEvOn_of_jump` — structurally, **every** `RBM.MomentDuhamelCut.CutHypEvOn`
  whose own fields satisfy `Kmod ≤ 2 * γ` is unsatisfiable, event or no event.

So the event restriction of §9 is necessary but **not** sufficient: the exponent has to grow
with `D` as well.  This section carries `(K_mod, γ)` through the §9 chain, from the entrywise
field to the (5.48) slot, using the blocks T258 left in `Flow/Eq548Producer.lean`
(`RBM.EntryModulusEvKOn`, `RBM.meshK`, `RBM.mesh_fine_at_meshK`, `RBM.card_le_at_meshK`).

Nothing of §9 is changed: `RBM.EntryModulusEvOn`, `RBM.Eq548EntryDataEvOn`,
`RBM.Eq548EntryDataEvOn'` and `RBM.flowEq548Sm_of_entryDataEvOn` keep their signatures byte for
byte, and `RBM.entryModulusEvKOn_one_half_iff` is the `Iff.rfl` certificate that the new field
at `(1, 1/2)` **is** the old proposition.

The pair the flow is to be produced at is D17's, `K_mod = D - 1`, `γ = 1/2`; at `D ≥ 60` this
is `K_mod ≥ 59 > 1 = 2γ`, outside T258's refuted range
(`RBM.not_cutHypEvOnK_kmod_le_two_gamma_d17`). -/

section EntriesEvOnK

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E D : ℝ} {s t : ℕ → ℝ}
variable {Good : ℕ → Set Ω} {Kmod γ : ℝ}

/-- **The parametric field at `(1, 1/2)` is the field of §9** — the same proposition, by
`rfl`, not an implication.  This is the certificate that nothing was strengthened: every
statement below, read at `Kmod = 1`, `γ = 1/2`, is the §9 statement. -/
theorem entryModulusEvKOn_one_half_iff (X : Sample B) (Good : ℕ → Set Ω) :
    EntryModulusEvKOn X E s t D 1 (1 / 2) Good ↔ EntryModulusEvOn X E s t D Good := Iff.rfl

theorem entryModulusEvKOn_of_entryModulusEvOn (X : Sample B)
    (h : EntryModulusEvOn X E s t D Good) : EntryModulusEvKOn X E s t D 1 (1 / 2) Good := h

theorem entryModulusEvOn_of_entryModulusEvKOn (X : Sample B)
    (h : EntryModulusEvKOn X E s t D 1 (1 / 2) Good) : EntryModulusEvOn X E s t D Good := h

/-- **`RBM.MomentDuhamelCut.CutHypEvOn` for `J*^{sm}_{u,D}` at an arbitrary admissible pair.**
Field for field `RBM.cutHypEvOn_jSfarSm_of_entries`, with `Kmod`, `γ`, the mesh `RBM.meshK` and
`Ccard = Kmod/γ + 1` all moving together.  `mesh_fine` and `card_le` — the two fields that pull
in opposite directions — are T258's *theorems* at that one mesh, so the parametrization cannot
make the bundle unsatisfiable through them. -/
noncomputable def cutHypEvOn_jSfarSm_of_entriesK (X : Sample B) (hK : 0 ≤ Kmod) (hγ : 0 < γ)
    (hst : ∀ N, s N ≤ t N) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    (hgm : ∀ N, MeasurableSet (Good N))
    (hmod : EntryModulusEvKOn X E s t D Kmod γ Good)
    (hmoment : ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ ε > (0 : ℝ), ∀ p : ℕ, ∃ C > (0 : ℝ),
      ∀ᶠ N : ℕ in atTop,
      ∀ ws ∈ MomentDuhamelCut.netFinset s t (meshK Kmod γ) N,
        ∫ ω, |MomentDuhamelCut.cutTrunc ((N : ℝ) ^ (2 * δ) * 1)
              (Step2FarMart.jSfarSm X E D N ws ω)| ^ (2 * p) ∂B.P
          ≤ C * ((N : ℝ) ^ (ε * p) * (1 : ℝ) ^ (2 * p))) :
    MomentDuhamelCut.CutHypEvOn B.P (fun N u ω => Step2FarMart.jSfarSm X E D N u ω) s t
      (fun _ => 1) Good where
  window := hst
  δ₀ := 1
  δ₀_pos := one_pos
  Θ_pos := fun _ => one_pos
  J_nonneg := fun _ _ _ => Step2FarMart.jSfarSm_nonneg X
  meas := fun N u => (measurable_jSfarSm X E D N u).aestronglyMeasurable
  good_meas := hgm
  mesh := meshK Kmod γ
  mesh_pos := meshK_pos Kmod γ
  Kmod := Kmod
  γ := γ
  γ_pos := hγ
  modulus := modulusEvAtOn_of_entryModulusEvKOn X hmod
  mesh_fine := Filter.Eventually.of_forall (mesh_fine_at_meshK hK hγ)
  Ccard := Kmod / γ + 1
  card_le := card_le_at_meshK hK hγ hs0 ht1
  moment := hmoment

/-- The bundle's own exponents are the pair it was built at — `rfl`, so T258's structural
verdict `RBM.not_cutHypEvOn_of_jump` applies to it exactly through `Kmod ≤ 2 * γ`. -/
theorem cutHypEvOn_jSfarSm_of_entriesK_Kmod (X : Sample B) (hK : 0 ≤ Kmod) (hγ : 0 < γ)
    (hst : ∀ N, s N ≤ t N) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    (hgm : ∀ N, MeasurableSet (Good N))
    (hmod : EntryModulusEvKOn X E s t D Kmod γ Good)
    (hmoment : ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ ε > (0 : ℝ), ∀ p : ℕ, ∃ C > (0 : ℝ),
      ∀ᶠ N : ℕ in atTop,
      ∀ ws ∈ MomentDuhamelCut.netFinset s t (meshK Kmod γ) N,
        ∫ ω, |MomentDuhamelCut.cutTrunc ((N : ℝ) ^ (2 * δ) * 1)
              (Step2FarMart.jSfarSm X E D N ws ω)| ^ (2 * p) ∂B.P
          ≤ C * ((N : ℝ) ^ (ε * p) * (1 : ℝ) ^ (2 * p))) :
    (cutHypEvOn_jSfarSm_of_entriesK X hK hγ hst hs0 ht1 hgm hmod hmoment).Kmod = Kmod ∧
      (cutHypEvOn_jSfarSm_of_entriesK X hK hγ hst hs0 ht1 hgm hmod hmoment).γ = γ :=
  ⟨rfl, rfl⟩

/-- **`J*^{sm}_{u,D} ≺ 1` from the event-restricted entrywise data at an arbitrary admissible
pair** — verbatim `RBM.stochDom_jSfarSm_of_entriesEvOn` with the exponents carried.  The
conclusion is **unchanged**: a `RBM.StochDom` for the honest, unrestricted functional. -/
theorem stochDom_jSfarSm_of_entriesEvOnK (X : Sample B) (hK : 0 ≤ Kmod) (hγ : 0 < γ)
    (hst : ∀ N, s N ≤ t N) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    (hgm : ∀ N, MeasurableSet (Good N)) (hgood : HighProb B.P Good)
    (hmod : EntryModulusEvKOn X E s t D Kmod γ Good)
    (hmoment : ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ ε > (0 : ℝ), ∀ p : ℕ, ∃ C > (0 : ℝ),
      ∀ᶠ N : ℕ in atTop,
      ∀ ws ∈ MomentDuhamelCut.netFinset s t (meshK Kmod γ) N,
        ∫ ω, |MomentDuhamelCut.cutTrunc ((N : ℝ) ^ (2 * δ) * 1)
              (Step2FarMart.jSfarSm X E D N ws ω)| ^ (2 * p) ∂B.P
          ≤ C * ((N : ℝ) ^ (ε * p) * (1 : ℝ) ^ (2 * p)))
    (hinit : StochDom B.P (fun N (_ : Unit) ω => Step2FarMart.jSfarSm X E D N (s N) ω)
      (fun _ _ _ => (1 : ℝ))) :
    StochDom B.P (fun N (u : TimeIcc s t N) ω => Step2FarMart.jSfarSm X E D N (u : ℝ) ω)
      (fun _ _ _ => (1 : ℝ)) :=
  letI := B.isProbabilityMeasure
  MomentDuhamelCut.stochDom_of_cutHypEvOn
    (cutHypEvOn_jSfarSm_of_entriesK X hK hγ hst hs0 ht1 hgm hmod hmoment) hgood
    (Filter.Eventually.of_forall fun _ => le_rfl) hinit

/-- **The entrywise data of (5.48) with the modulus restricted to `Good` and its exponents as
parameters** — `near` is byte for byte the field of `RBM.Eq548EntryDataEvOn`; `modulus` and
`moment` carry `(Kmod, γ)` (the latter through the matching net `RBM.meshK`). -/
structure Eq548EntryDataEvOnK (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) (Kmod γ : ℝ)
    (Good : ℕ → Set Ω) : Prop where
  near : ∀ D : ℝ, 0 < D → StochDom B.P
    (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
      X.lkErr E N p.1 ω (pmLoop p.2.1 p.2.2))
    (fun N p _ => (etaT E (s N) / etaT E p.1) ^ 2 *
      tailT (B.W N : ℝ) (B.ell N p.1) (etaT E p.1) D (zdist (B.L N) (p.2.1 - p.2.2)))
  modulus : ∀ D : ℝ, 0 < D → EntryModulusEvKOn X E s t D Kmod γ Good
  moment : ∀ D : ℝ, 0 < D → ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ ε > (0 : ℝ), ∀ p : ℕ, ∃ C > (0 : ℝ),
    ∀ᶠ N : ℕ in atTop,
    ∀ ws ∈ MomentDuhamelCut.netFinset s t (meshK Kmod γ) N,
      ∫ ω, |MomentDuhamelCut.cutTrunc ((N : ℝ) ^ (2 * δ) * 1)
            (Step2FarMart.jSfarSm X E D N ws ω)| ^ (2 * p) ∂B.P
        ≤ C * ((N : ℝ) ^ (ε * p) * (1 : ℝ) ^ (2 * p))

/-- **The (5.48) slot at the shape the satisfiability discipline allows, with exponents.**
Exactly `RBM.Eq548EntryDataEvOn'` with `(Kmod, γ)` free: the event is existentially quantified
together with its measurability and its high probability, and `RBM.HighProb` is what rules out
the vacuous `Good = ∅`. -/
def Eq548EntryDataEvOnK' (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) (Kmod γ : ℝ) : Prop :=
  ∃ Good : ℕ → Set Ω, (∀ N, MeasurableSet (Good N)) ∧ HighProb B.P Good ∧
    Eq548EntryDataEvOnK X E s t Kmod γ Good

/-- **At `(1, 1/2)` the parametric package is §9's, field for field.**  `near` and `modulus`
are the same propositions (`RBM.entryModulusEvKOn_one_half_iff`); `moment` differs only in that
the net is written `RBM.meshK 1 (1/2)` instead of `(N+1)²`, and `RBM.meshK_one_half` says those
are the same function. -/
theorem Eq548EntryDataEvOn.toK_one_half {X : Sample B}
    (H : Eq548EntryDataEvOn X E s t Good) :
    Eq548EntryDataEvOnK X E s t 1 (1 / 2) Good where
  near := H.near
  modulus := fun D hD => H.modulus D hD
  moment := by rw [meshK_one_half]; exact H.moment

/-- The same at the slot level, so §13's table below is no harder to satisfy at `(1, 1/2)`
than §9's. -/
theorem Eq548EntryDataEvOn'.toK_one_half {X : Sample B} (H : Eq548EntryDataEvOn' X E s t) :
    Eq548EntryDataEvOnK' X E s t 1 (1 / 2) := by
  obtain ⟨Good, hgm, hgood, H⟩ := H
  exact ⟨Good, hgm, hgood, H.toK_one_half⟩

/-- **The (5.48) slot from the event-restricted entrywise data at an arbitrary admissible
pair** — verbatim `RBM.flowEq548Sm_of_entryDataEvOn` with `(Kmod, γ)` carried through. -/
theorem flowEq548Sm_of_entryDataEvOnK (X : Sample B) (hK : 0 ≤ Kmod) (hγ : 0 < γ)
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hc : Cond272 B E s t)
    (hB : BoundsCore X E s) (H : Eq548EntryDataEvOnK' X E s t Kmod γ) :
    FlowEq548Sm X E s t := by
  obtain ⟨Good, hgm, hgood, H⟩ := H
  exact flowEq548Sm_of_nearChi X ht1
    (Step2FarMart.flowEq548W_of_jSfarSm X H.near fun D hD =>
      stochDom_jSfarSm_of_entriesEvOnK X hK hγ hst hs0 ht1 hgm hgood (H.modulus D hD)
        (H.moment D hD)
        (stochDom_jSfarSm_init_of_boundsCore X (t := t) hE hst ht1 hc hB D hD))

/-! #### Satisfiability: the pair the slot is to be produced at

T258's refutation is sharp: `RBM.not_cutHypEvOn_of_jump` kills a bundle **iff** its own fields
satisfy `Kmod ≤ 2 * γ`.  D17's pair `(D - 1, 1/2)` at `D ≥ 60` is `(≥ 59, 1/2)`, and
`59 > 1 = 2 * (1/2)`, so it is outside that range — the gate below is compiled, not asserted. -/

/-- **The gate.**  At `γ = 1/2` and `Kmod = D - 1` with `D ≥ 60`, the hypothesis
`Kmod ≤ 2 * γ` of `RBM.not_cutHypEvOn_of_jump` and of
`RBM.not_entryModulusEvKOn_swapSample_of_far` is **false**.  Compare
`RBM.d17_pair_outside_event_refutation`, which is this at `D = 60`. -/
theorem d17K_outside_jump_refutation {D : ℝ} (hD : 60 ≤ D) :
    ¬ ((D - 1 : ℝ) ≤ 2 * (1 / 2 : ℝ)) := by intro h; linarith

/-- `0 ≤ Kmod` and `0 < γ` at D17's pair, the two side conditions of
`RBM.cutHypEvOn_jSfarSm_of_entriesK`.  `0 < γ` is not cosmetic: at `γ = 0` the field would be
an absolute bound `N^{Kmod}` and carry no modulus at all. -/
theorem d17K_admissible {D : ℝ} (hD : 60 ≤ D) : (0 : ℝ) ≤ D - 1 ∧ (0 : ℝ) < 1 / 2 :=
  ⟨by linarith, by norm_num⟩

/-- **The bundle this section builds at D17's pair is not the one T258 refuted.**  The
statement is about the very bundle `RBM.cutHypEvOn_jSfarSm_of_entriesK` produces: its own
`Kmod` and `γ` fields fail the hypothesis of `RBM.not_cutHypEvOn_of_jump`, so that theorem
cannot be applied to it.  This is the anti-vacuity gate of T261. -/
theorem not_cutHypEvOnK_kmod_le_two_gamma_d17 (X : Sample B) {D : ℝ} (hD : 60 ≤ D)
    (hst : ∀ N, s N ≤ t N) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    (hgm : ∀ N, MeasurableSet (Good N))
    (hmod : EntryModulusEvKOn X E s t D (D - 1) (1 / 2) Good)
    (hmoment : ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ ε > (0 : ℝ), ∀ p : ℕ, ∃ C > (0 : ℝ),
      ∀ᶠ N : ℕ in atTop,
      ∀ ws ∈ MomentDuhamelCut.netFinset s t (meshK (D - 1) (1 / 2)) N,
        ∫ ω, |MomentDuhamelCut.cutTrunc ((N : ℝ) ^ (2 * δ) * 1)
              (Step2FarMart.jSfarSm X E D N ws ω)| ^ (2 * p) ∂B.P
          ≤ C * ((N : ℝ) ^ (ε * p) * (1 : ℝ) ^ (2 * p))) :
    ¬ ((cutHypEvOn_jSfarSm_of_entriesK X (D := D) (Kmod := D - 1) (γ := 1 / 2)
          (by linarith) (by norm_num) hst hs0 ht1 hgm hmod hmoment).Kmod
        ≤ 2 * (cutHypEvOn_jSfarSm_of_entriesK X (D := D) (Kmod := D - 1) (γ := 1 / 2)
          (by linarith) (by norm_num) hst hs0 ht1 hgm hmod hmoment).γ) :=
  d17K_outside_jump_refutation hD

/-- **A compiled witness that the parametric field is satisfiable at D17's pair**, on the
degenerate window `t = s` and on any event: T258's `RBM.sat_entryModulusEvK_of_window_point`
transported to the event shape.  `0 < γ` is what makes the right-hand side `N^{Kmod} · 0^γ`
vanish, so this witness is the reason `γ > 0` is kept. -/
theorem sat_entryModulusEvKOn_d17 (X : Sample B) (Good : ℕ → Set Ω) (ht : ∀ N, t N = s N) :
    EntryModulusEvKOn X E s t D (D - 1) (1 / 2) Good :=
  entryModulusEvKOn_of_entryModulusEvK X Good
    (sat_entryModulusEvK_of_window_point X (by norm_num) ht)

end EntriesEvOnK

/-! ### 11. Deviations from the paper introduced here (T261)

**`T261a` — the entrywise modulus of (5.46) carries its exponents, and the flow is produced at
`K_mod = D - 1`, `γ = 1/2` rather than at `K_mod = 1`.**

① **Paper location.**  §5.3, the display (5.46) and the chaining argument that consumes it;
the exponent in question is the `N` power on the right-hand side of the entrywise two-sided
modulus of `L - K` used to pass from the net to the full window.

② **Is the paper wrong / must it change?**  Yes, one constant has to change.  The printed
argument reads as if a modulus with an `O(N)` constant sufficed.  It does not: T258's
`RBM.not_entryModulusEvKOn_one_half_bandGrow` is a compiled refutation of that reading on a
concrete band model, with `2 ≤ D` its only premise, and `RBM.not_cutHypEvOn_of_jump` shows the
obstruction is structural — any modulus with `K_mod ≤ 2γ` is refuted by the jump of
`J*^{sm}` at `v = N^{-2}`, whose size is `≍ W_N → ∞`.  Since the tail exponent `D` is free and
the jump is governed by it, the exponent of the modulus must be allowed to grow with `D`; the
value carried here is D17's `K_mod = D - 1` at `γ = 1/2`, which is outside the refuted range
(`RBM.d17K_outside_jump_refutation`).  The event restriction of `T251a` is still needed — the
two repairs are independent and neither alone suffices.

③ **Size of the change.**  One symbol in (5.46) (`N` ⤳ `N^{D-1}`), plus one sentence saying
that the net `RBM.meshK` is refined to match (`m_N = (N+1)^{K_mod/γ}`), which is what keeps the
chaining error at `O(1)`.  Nothing downstream of (5.48) changes: the conclusion of the chaining
argument is unchanged.

④ **Renumbering.**  None: nothing is inserted before an existing numbered display.
-/

end RBM
