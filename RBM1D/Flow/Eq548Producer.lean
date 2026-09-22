/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.Step2FarMart
import RBM1D.Hierarchy.Step2Near47
import RBM1D.Defs.MatrixMeasurable
import RBM1D.Gauss.FlowHolder
import RBM1D.Gauss.LoopLipschitz

/-!
# Producers for the entrywise data of (5.48): `near`, `meas`, `modulus` (T244)

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.3, (5.47)–(5.48).

`RBM.Step2FarMart.flowEq548W_of_entries` (T228) — equivalently the five fields of
`RBM.Eq548EntryData` (T239) — produces (5.48) in the smoothed shape from five pieces of data:
`hnear`, `hmeas`, `hmod`, `hmoment`, `hinit`.  This file settles the first three.

## Main results

### §1 `meas`, **discharged outright**

* `RBM.measurable_H`, `RBM.measurable_green_apply`, `RBM.measurable_Gsig_apply`,
  `RBM.measurable_mul_apply`, `RBM.measurable_gloopProd_apply`, `RBM.measurable_Lval`,
  `RBM.measurable_lk`, `RBM.measurable_lkFarSm` — the measurability chain from the single
  field `RBM.Sample.measurable` (`ω ↦ (H_u)_{ij}` measurable) up to the loop error.  The one
  non-continuous step is the matrix inverse, and that is `RBM.Gauss.measurable_matrix_inv_apply`
  (`Defs/MatrixMeasurable.lean`); everything else (`det`, `adjugate`, matrix product, `trace`,
  `Finset.sup'`) is continuous or a finite lattice/ring operation.
* `RBM.measurable_jSfarSm`, `RBM.aestronglyMeasurable_jSfarSm` — **the `meas` field, with no
  hypotheses at all**: `J*^{sm}_{u,D}` is measurable in `ω` for every `Sample`.  So this field
  is not an assumption any more, and it cannot be vacuous.

### §2 `near`, **wired**

* `RBM.near_of_sharp` — the `near` field *is* `RBM.Step2Near47.hnear_sharp`, i.e. T207's sharp
  (5.47) `J*_{u,D} ≺ (η_s/η_u)²`.  No new mathematics; the field stops being an independent
  assumption and becomes the sharp moment interface `RBM.Step2Near47.MomentHypCutSharp`.
* `RBM.flowEq548W_of_sharp_entries` — (5.48) at the smooth weight with **`hmeas` absent and
  `hnear` replaced by `MomentHypCutSharp`**.  Remaining inputs: `hmod`, `hmoment`, `hinit`.

### §3 `modulus`, **proved false in the `∀ N` shape** (and exactly how)

`RBM.EntryModulus` is T228's `hmod` verbatim (at one `D`).  Two defects, both compiled:

* `RBM.modulus_ratio_const_at_zero`, `RBM.modulus_jSfarSm_const_at_zero` — at `N = 0` the
  right-hand side is `0^1 · |v-w|^{1/2} = 0`, so the request is not a modulus at all: it
  **forces `v ↦ ‖(L-K)_v‖/T_v` to be constant on the whole window `[s₀, t₀]`, for every `ω`**,
  and hence `J*^{sm}_{·,D}` to be constant there.  This is the same `∀ N`-versus-`∀ᶠ N` defect
  T232 found for `RBM.MomentDuhamelCut.CutHyp.modulus` with a genuinely time-dependent
  threshold, and it is independent of `Kmod` and `γ`
  (`RBM.modulus_rhs_eq_zero_at_zero` is stated for arbitrary exponents).
* `RBM.not_entryModulus_of_jSfarSm_ne`, `RBM.not_entryModulus_of_ratio_ne` — the contrapositive:
  as soon as the window `[s₀, t₀]` is nondegenerate and the normalized loop error moves inside
  it at a single `ω`, **no `hmod` exists**.
* `RBM.sat_entryModulus_of_window_point` — the negative is sharp, not an artifact: on a
  degenerate window (`t N = s N` for all `N`) `hmod` does hold.  So the field is satisfiable
  exactly when it says nothing.
* `RBM.entryModulus_uniform_in_omega` — the second defect, orthogonal to the first: even at
  `N ≥ 1` the request is a **deterministic inequality quantified over all `ω`**, while the
  factor `‖(L-K)_v‖/T_v(d)` it multiplies is only `≺ 1` (its deterministic bound through
  `T ≥ W^{-D}` is `W^D`, and `D ≥ 60` downstream).  This is the forbidden pattern of the
  satisfiability discipline; the field has to be restricted to a `HighProb` event.

### §5 the repaired route

* `RBM.EntryModulusEv` — the same field with `∀ N` replaced by `∀ᶠ N in atTop`, and
  `RBM.entryModulusEv_of_entryModulus`.
* `RBM.cutHypEv_jSfarSm_of_entries`, `RBM.stochDom_jSfarSm_of_entriesEv`,
  `RBM.flowEq548W_of_sharp_entriesEv` — the (5.48) chain routed through T232's
  `RBM.MomentDuhamelCut.CutHypEv` (`modulus`/`mesh_fine` asymptotic) instead of
  `RBM.MomentDuhamelCut.CutHyp`.  Nothing else in the chain changes, `hmeas` is discharged by
  §1, `hnear` comes from §2, and the only inputs left are `hmoment` and `hinit`.

### §6 satisfiability

* `RBM.meas_target_nondegenerate` — the field §1 closes is a statement about an object that is
  `≥ 1` everywhere (`RBM.Step2FarMart.one_le_jSfarSm`), for every `ω` including `ω = 0`; §1 has
  **no hypotheses at all**, so it cannot be vacuous.
* `RBM.sat_entryModulus_of_window_point`, `RBM.sat_entryModulusEv_of_window_point` — the
  degenerate witness that makes §3's negative sharp.
* That `EntryModulusEv` is *strictly* weaker than `EntryModulus`, at the flow's own
  `Kmod = 1`, `γ = 1/2`, `Θ ≡ 1`, is T232's `RBM.MomentDuhamelCut.satCutHypEv` together with
  `RBM.MomentDuhamelCut.sat_modulus_not_forall`.

### §11–§14 T258: the exponents `(Kmod, γ)` become parameters, and the verdict on a real model

* `RBM.EntryModulusEvK`, `RBM.EntryModulusEvKOn` — `RBM.EntryModulusEv` with
  `(N : ℝ)^1 |v - w|^{1/2}` replaced by `(N : ℝ)^{Kmod} |v - w|^γ`, unrestricted and on an
  event.  `RBM.entryModulusEvK_one_half` is the `Iff.rfl` certificate that at `(1, 1/2)` the
  parametric field *is* the old one; `RBM.meshK`, `RBM.meshK_one_half`,
  `RBM.mesh_fine_at_meshK`, `RBM.card_le_at_meshK` move the net with the exponents, and at
  `(1, 1/2)` reproduce the old `(N+1)²` and `Ccard = 3`.  Old names, bodies and consumers are
  untouched.
* `RBM.cutHypEv_jSfarSm_of_entriesK`, `RBM.stochDom_jSfarSm_of_entriesEvK`,
  `RBM.flowEq548W_of_sharp_entriesEvK` — the (5.48) chain at an arbitrary admissible pair.
* `RBM.not_entryModulusEvK_swapSample_of_far` — **the verdict holds for every `Kmod : ℝ` and
  every `γ > 0`** on a window starting at `0`: parametrizing does not rescue the field.
* `RBM.exists_jSfarSm_ge_swapSample'`, `RBM.gap_lower_mul_W` — the two sharpenings the event
  argument needs (the witness's size; the factor `W` that `RBM.gap_lower` discards).
* `RBM.not_entryModulusEvKOn_swapSample_of_far` — **on the event `{|ω| ≤ N}` the verdict holds
  exactly for `Kmod ≤ 2γ`**, which contains the hard-coded `(1, 1/2)`.
* `RBM.bandR`, `RBM.bandGrow`, `RBM.hsep_bandGrow`, `RBM.not_entryModulusEv_bandGrow`,
  `RBM.not_cutHypEv_bandGrow`, `RBM.not_entryModulusEvKOn_one_half_bandGrow` — T252's `hsep`
  wired in, so all of the above hold **unconditionally on one concrete model**.

## What this file does **not** close

`hmoment` (T230/T210) and `hinit` (T241) stay as they were.  `hmod` is **not** closed: §3
refutes the `∀ N` shape and §5 gives the route that avoids it, but the `∀ᶠ N` field itself is
still an input, and by §3's second half it will also need an event restriction, since the
factor `‖(L-K)_v‖/T_{v,D}` it multiplies is only `≺ 1`.  Making
`RBM.Step2FarMart.cutHyp_jSfarSm_of_entries` itself go through `CutHypEv` is a one-field edit
in `Hierarchy/Step2FarMart.lean`, which this ticket may not touch.

## Deviations from the paper

**None; no numbered `paper-delta` entry (temporary number `T244a` not used).**  §1 and §2 are a
technical measurability chain and a wiring of two existing statements, neither of which touches
a statement of the paper.  §3 is about the shape of a repository-internal hypothesis introduced
by T228 (the paper's (5.48) has no such field; the paper's argument runs the continuity of
`u ↦ J*_u` on a stopping-time argument, not on a uniform modulus), so it is a statement about
the formalization, not a departure from the text.
-/

namespace RBM

open MeasureTheory Filter Matrix

/-! ### 1. `meas`: `J*^{sm}_{u,D}` is measurable in `ω`, unconditionally

The only step that is not a continuous algebraic operation is the matrix inverse inside
`RBM.green`; `RBM.Gauss.measurable_matrix_inv_apply` handles it once and for all. -/

section Meas

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- `ω ↦ H_u(ω)` is measurable as a *matrix*-valued map, from the entrywise field
`RBM.Sample.measurable`. -/
theorem measurable_H (X : Sample B) (N : ℕ) (u : ℝ) : Measurable fun ω => X.H N u ω :=
  Measurable.of_eval_matrix _ fun i j => X.measurable N u i j

/-- Entries of the resolvent `G = (H_u - z)⁻¹` are measurable in `ω`. -/
theorem measurable_green_apply (X : Sample B) (N : ℕ) (u : ℝ) (z : ℂ) (i j : B.Idx N) :
    Measurable fun ω => green (X.H N u ω) z i j := by
  refine Gauss.measurable_matrix_inv_apply (M := fun ω => X.H N u ω - z • 1) ?_ i j
  exact Measurable.of_eval_matrix _ fun a b => (X.measurable N u a b).sub measurable_const

/-- The same for `G(σ)` of Definition 2.9 (`z` for `σ = +`, `z̄` for `σ = -`). -/
theorem measurable_Gsig_apply (X : Sample B) (N : ℕ) (u : ℝ) (z : ℂ) (σ : Bool)
    (i j : B.Idx N) : Measurable fun ω => Gsig (X.H N u ω) z σ i j := by
  cases σ
  · simpa [Gsig] using measurable_green_apply X N u ((starRingEnd ℂ) z) i j
  · simpa [Gsig] using measurable_green_apply X N u z i j

/-- Entries of a product of two matrix-valued maps with measurable entries are measurable
(`(AC)_{ij} = ∑_k A_{ik}C_{kj}`, a finite sum). -/
theorem measurable_mul_apply {ι : Type*} [Fintype ι] {A C : Ω → Matrix ι ι ℂ}
    (hA : ∀ i j, Measurable fun ω => A ω i j) (hC : ∀ i j, Measurable fun ω => C ω i j)
    (i j : ι) : Measurable fun ω => (A ω * C ω) i j := by
  simp only [Matrix.mul_apply]
  exact Finset.measurable_sum _ fun k _ => (hA i k).mul (hC k j)

/-- Entries of the loop product `∏_i G(σ_i)E_{a_i}` of (2.41) are measurable in `ω`.  The
induction is on the zipped charge/label list that `RBM.gloopProd` folds over; `RBM.Eblk` is
deterministic. -/
theorem measurable_gloopProd_apply (X : Sample B) (N : ℕ) (u : ℝ) (z : ℂ)
    (I : LoopIdx (ZMod (B.L N))) (i j : B.Idx N) :
    Measurable fun ω => gloopProd (B.L N) (B.W N) (X.H N u ω) z I i j := by
  suffices h : ∀ l : List (Bool × ZMod (B.L N)), ∀ i j : B.Idx N,
      Measurable fun ω => (l.foldr
        (fun (p : Bool × ZMod (B.L N)) (M : Matrix (B.Idx N) (B.Idx N) ℂ) =>
          Gsig (X.H N u ω) z p.1 * Eblk (B.L N) (B.W N) p.2 * M) 1) i j by
    simpa [gloopProd] using h (I.σ.zip I.a) i j
  intro l
  induction l with
  | nil => intro i j; simp
  | cons p l ih =>
      intro i j
      simp only [List.foldr_cons]
      refine measurable_mul_apply ?_ (fun a b => ih a b) i j
      intro a b
      refine measurable_mul_apply (fun c d => measurable_Gsig_apply X N u z p.1 c d)
        (C := fun _ => Eblk (B.L N) (B.W N) p.2) (fun _ _ => measurable_const) a b

/-- **The loop `L_{u,σ,a}` of (2.41) is measurable in `ω`** — the trace of the loop product. -/
theorem measurable_Lval (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ)
    (I : LoopIdx (ZMod (B.L N))) : Measurable fun ω => X.Lval E N u ω I := by
  have h : ∀ ω : Ω, X.Lval E N u ω I
      = ∑ i : B.Idx N, gloopProd (B.L N) (B.W N) (X.H N u ω) (zt E u) I i i := fun _ => rfl
  simp only [h]
  exact Finset.measurable_sum _ fun i _ => measurable_gloopProd_apply X N u _ I i i

/-- **`(L - K)_{u,(+,-),a}` is measurable in `ω`** (`K` is deterministic). -/
theorem measurable_lk (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (a : LoopArg (B.L N) 2) :
    Measurable fun ω => Step2.lk X E N u ω a := by
  change Measurable fun ω => X.Lval E N u ω (LoopData.idx (Step2.sigPM, a))
      - B.Kval E N u (LoopData.idx (Step2.sigPM, a))
  exact (measurable_Lval X E N u (LoopData.idx (Step2.sigPM, a))).sub measurable_const

/-- The far-weighted loop error is measurable in `ω` (the weight is deterministic). -/
theorem measurable_lkFarSm (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (a : LoopArg (B.L N) 2) :
    Measurable fun ω => Step2FarMart.lkFarSm X E N u ω a := by
  change Measurable fun ω => Step2FarMart.farChi (B.W N : ℝ) (B.ell N u)
      (zdist (B.L N) (a 0 - a 1)) * ‖Step2.lk X E N u ω a‖
  exact measurable_const.mul (measurable_lk X E N u a).norm

/-- **`J*^{sm}_{u,D}` is measurable in `ω`** — a finite `Finset.sup'` of the measurable ratios
`(1-χ)‖(L-K)_{u,a}‖/T_{u,D}(‖a₁-a₂‖)`, plus `1`. -/
theorem measurable_jSfarSm (X : Sample B) (E D : ℝ) (N : ℕ) (u : ℝ) :
    Measurable fun ω => Step2FarMart.jSfarSm X E D N u ω := by
  have h : ∀ ω : Ω, Step2FarMart.jSfarSm X E D N u ω
      = (Finset.univ.sup' Finset.univ_nonempty
          (fun (a : LoopArg (B.L N) 2) (ω' : Ω) =>
            Step2FarMart.lkFarSm X E N u ω' a / tailT (B.W N : ℝ) (B.ell N u) (etaT E u) D
              (zdist (B.L N) (a 0 - a 1)))) ω + 1 := by
    intro ω; rw [Finset.sup'_apply]; rfl
  simp only [h]
  exact (Finset.measurable_sup' _ fun a _ =>
    (measurable_lkFarSm X E N u a).div measurable_const).add measurable_const

/-- **The `meas` field of `RBM.Eq548EntryData`, with no hypotheses.**  This is the `hmeas`
slot of `RBM.Step2FarMart.flowEq548W_of_entries` and of
`RBM.Step2FarMart.cutHyp_jSfarSm_of_entries`, in the exact shape they ask for. -/
theorem aestronglyMeasurable_jSfarSm (X : Sample B) (E : ℝ) :
    ∀ D : ℝ, 0 < D → ∀ (N : ℕ) (u : ℝ),
      AEStronglyMeasurable (fun ω => Step2FarMart.jSfarSm X E D N u ω) B.P :=
  fun D _ N u => (measurable_jSfarSm X E D N u).aestronglyMeasurable

end Meas

/-! ### 2. `near`: T207's sharp (5.47), wired

`RBM.Step2Near47.hnear_sharp` already has the exact shape of the `near` field.  Naming it here
records that the field is no longer independent: it is the sharp moment interface
`RBM.Step2Near47.MomentHypCutSharp`. -/

section Near

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E : ℝ} {s t : ℕ → ℝ}
variable (X : Sample B)

/-- **The `near` field of `RBM.Eq548EntryData`, from the sharp (5.47)** (T207). -/
theorem near_of_sharp (Hy : ∀ D : ℝ, 0 < D → Step2Near47.MomentHypCutSharp X E s t D)
    (hE : |E| < 2) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) :
    ∀ D : ℝ, 0 < D → StochDom B.P
      (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
        X.lkErr E N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => (etaT E (s N) / etaT E p.1) ^ 2 *
        tailT (B.W N : ℝ) (B.ell N p.1) (etaT E p.1) D
          (zdist (B.L N) (p.2.1 - p.2.2))) :=
  Step2Near47.hnear_sharp X Hy hE hst ht1

end Near

/-! ### 3. `modulus`: the request, and why it is false in this shape -/

section Modulus

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- **T228's entrywise two-sided modulus, verbatim** (the `hmod` slot of
`RBM.Step2FarMart.flowEq548W_of_entries` at one `D`, i.e. the `modulus` field of
`RBM.Eq548EntryData` at one `D`).

The first summand is what the smoothing of `RBM.Step2FarMart.nearChi` buys (the sharp indicator
gives a whole jump, `RBM.Step2FarMart.lkFar_crossing`); the second is the time-regularity of the
normalized loop error itself, which the smoothing does **not** touch. -/
def EntryModulus (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) (D : ℝ) : Prop :=
  ∀ (N : ℕ) (ω : Ω), ∀ v ∈ Set.Icc (s N) (t N), ∀ w ∈ Set.Icc (s N) (t N),
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

variable {E D : ℝ} {s t : ℕ → ℝ} (X : Sample B)

/-- **The right-hand side vanishes at `N = 0`, for every `Kmod` and every `γ`.**  So the
`∀ N` shape is not a modulus of continuity at `N = 0`: it is an equality constraint.  Exactly
T232's defect for `RBM.MomentDuhamelCut.CutHyp.modulus`. -/
theorem modulus_rhs_eq_zero_at_zero (Kmod γ : ℝ) (hK : Kmod ≠ 0) (r : ℝ) :
    ((0 : ℕ) : ℝ) ^ Kmod * r ^ γ = 0 := by
  rw [Nat.cast_zero, Real.zero_rpow hK, zero_mul]

/-- **`hmod` forces the normalized loop error to be constant in time at `N = 0`** — for *every*
sample point `ω`, every label pair `x`, and every pair of times in the window `[s₀, t₀]`. -/
theorem modulus_ratio_const_at_zero (h : EntryModulus X E s t D) (ω : Ω)
    {v : ℝ} (hv : v ∈ Set.Icc (s 0) (t 0)) {w : ℝ} (hw : w ∈ Set.Icc (s 0) (t 0))
    (x : LoopArg (B.L 0) 2) :
    ‖Step2.lk X E 0 v ω x‖ / tailT (B.W 0 : ℝ) (B.ell 0 v) (etaT E v) D
        (zdist (B.L 0) (x 0 - x 1))
      = ‖Step2.lk X E 0 w ω x‖ / tailT (B.W 0 : ℝ) (B.ell 0 w) (etaT E w) D
        (zdist (B.L 0) (x 0 - x 1)) := by
  have h0 := h 0 ω v hv w hw x
  rw [modulus_rhs_eq_zero_at_zero 1 ((1 : ℝ) / 2) one_ne_zero |v - w|] at h0
  have h1 : (0 : ℝ) ≤ 15 / 8 *
      |(zdist (B.L 0) (x 0 - x 1) : ℝ) / (6 * ellStar (B.W 0 : ℝ) (B.ell 0 v))
        - (zdist (B.L 0) (x 0 - x 1) : ℝ) / (6 * ellStar (B.W 0 : ℝ) (B.ell 0 w))|
      * |‖Step2.lk X E 0 v ω x‖ / tailT (B.W 0 : ℝ) (B.ell 0 v) (etaT E v) D
          (zdist (B.L 0) (x 0 - x 1))| := by positivity
  have h2 : |‖Step2.lk X E 0 v ω x‖ / tailT (B.W 0 : ℝ) (B.ell 0 v) (etaT E v) D
        (zdist (B.L 0) (x 0 - x 1))
      - ‖Step2.lk X E 0 w ω x‖ / tailT (B.W 0 : ℝ) (B.ell 0 w) (etaT E w) D
        (zdist (B.L 0) (x 0 - x 1))| ≤ 0 := by linarith
  have := abs_nonpos_iff.1 h2
  linarith [sub_eq_zero.1 this, this]

/-- **`hmod` forces `J*^{sm}_{·,D}` to be constant on the window at `N = 0`**, for every `ω` —
through `RBM.Step2FarMart.modulus_jSfarSm_of_entries`, i.e. exactly the way the `CutHyp`
consumes it. -/
theorem modulus_jSfarSm_const_at_zero (h : EntryModulus X E s t D) (ω : Ω)
    {v : ℝ} (hv : v ∈ Set.Icc (s 0) (t 0)) {w : ℝ} (hw : w ∈ Set.Icc (s 0) (t 0)) :
    Step2FarMart.jSfarSm X E D 0 v ω = Step2FarMart.jSfarSm X E D 0 w ω := by
  have h0 := Step2FarMart.modulus_jSfarSm_of_entries X (Kmod := 1) (γ := (1 : ℝ) / 2) h 0 ω
    v hv w hw
  rw [modulus_rhs_eq_zero_at_zero 1 ((1 : ℝ) / 2) one_ne_zero |v - w|] at h0
  have := abs_nonpos_iff.1 h0
  linarith [sub_eq_zero.1 this]

/-- **The contrapositive: no `hmod` exists** as soon as `J*^{sm}` really moves inside the
`N = 0` window at one sample point. -/
theorem not_entryModulus_of_jSfarSm_ne (ω : Ω)
    {v : ℝ} (hv : v ∈ Set.Icc (s 0) (t 0)) {w : ℝ} (hw : w ∈ Set.Icc (s 0) (t 0))
    (hne : Step2FarMart.jSfarSm X E D 0 v ω ≠ Step2FarMart.jSfarSm X E D 0 w ω) :
    ¬ EntryModulus X E s t D :=
  fun h => hne (modulus_jSfarSm_const_at_zero X h ω hv hw)

/-- The same from the entrywise ratio. -/
theorem not_entryModulus_of_ratio_ne (ω : Ω)
    {v : ℝ} (hv : v ∈ Set.Icc (s 0) (t 0)) {w : ℝ} (hw : w ∈ Set.Icc (s 0) (t 0))
    (x : LoopArg (B.L 0) 2)
    (hne : ‖Step2.lk X E 0 v ω x‖ / tailT (B.W 0 : ℝ) (B.ell 0 v) (etaT E v) D
          (zdist (B.L 0) (x 0 - x 1))
        ≠ ‖Step2.lk X E 0 w ω x‖ / tailT (B.W 0 : ℝ) (B.ell 0 w) (etaT E w) D
          (zdist (B.L 0) (x 0 - x 1))) :
    ¬ EntryModulus X E s t D :=
  fun h => hne (modulus_ratio_const_at_zero X h ω hv hw x)

/-- **The negative is sharp.**  On a degenerate window the field does hold — so `hmod` is
satisfiable exactly when it says nothing, and the defect really is the `∀ N` quantifier and not
a miscomputed constant. -/
theorem sat_entryModulus_of_window_point (ht : ∀ N, t N = s N) : EntryModulus X E s t D := by
  intro N ω v hv w hw x
  have hv' : v = s N := le_antisymm (by rw [← ht N]; exact hv.2) hv.1
  have hw' : w = s N := le_antisymm (by rw [← ht N]; exact hw.2) hw.1
  subst hv'
  subst hw'
  simp

/-- **The second defect, orthogonal to the first.**  Even at `N ≥ 1`, `hmod` is a
*deterministic* inequality quantified over **all** `ω`: it asks the normalized loop error to be
Hölder-`1/2` in time with an `ω`-independent constant `N`.  But `‖(L-K)_v‖/T_{v,D}` is only
`≺ 1` (`RBM.Step2Near47.jS_stochDom_sharp`); its deterministic bound goes through
`T_{v,D} ≥ W^{-D}` and is `W^D`, with `D ≥ 60` downstream.  By the satisfiability discipline
such a field must carry an event restriction (`ω ∈ Good`, `HighProb`, …). -/
theorem entryModulus_uniform_in_omega (h : EntryModulus X E s t D) (N : ℕ) (ω : Ω)
    {v : ℝ} (hv : v ∈ Set.Icc (s N) (t N)) {w : ℝ} (hw : w ∈ Set.Icc (s N) (t N))
    (x : LoopArg (B.L N) 2) :
    |‖Step2.lk X E N v ω x‖ / tailT (B.W N : ℝ) (B.ell N v) (etaT E v) D
          (zdist (B.L N) (x 0 - x 1))
        - ‖Step2.lk X E N w ω x‖ / tailT (B.W N : ℝ) (B.ell N w) (etaT E w) D
          (zdist (B.L N) (x 0 - x 1))|
      ≤ (N : ℝ) ^ (1 : ℝ) * |v - w| ^ ((1 : ℝ) / 2) := by
  have h0 := h N ω v hv w hw x
  have h1 : (0 : ℝ) ≤ 15 / 8 *
      |(zdist (B.L N) (x 0 - x 1) : ℝ) / (6 * ellStar (B.W N : ℝ) (B.ell N v))
        - (zdist (B.L N) (x 0 - x 1) : ℝ) / (6 * ellStar (B.W N : ℝ) (B.ell N w))|
      * |‖Step2.lk X E N v ω x‖ / tailT (B.W N : ℝ) (B.ell N v) (etaT E v) D
          (zdist (B.L N) (x 0 - x 1))| := by positivity
  linarith

end Modulus

/-! ### 4. (5.48) with `meas` and `near` discharged -/

section Assemble

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E : ℝ} {s t : ℕ → ℝ}
variable (X : Sample B)

/-- **(5.48) at the smooth weight, with two of the five slots gone.**  Compared with
`RBM.Step2FarMart.flowEq548W_of_entries`: `hmeas` has **disappeared** (§1 proves it), and
`hnear` is replaced by the sharp moment interface `RBM.Step2Near47.MomentHypCutSharp` (§2).

⚠ `hmod` is kept in the signature **only** because the frozen interface asks for it; §3 shows
it is false whenever the `N = 0` window is nondegenerate and the loop error moves in it, so
this theorem should be read as the *shape* of the remaining work, not as a route that can be
completed as written. -/
theorem flowEq548W_of_sharp_entries (hE : |E| < 2)
    (hst : ∀ N, s N ≤ t N) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    (Hy : ∀ D : ℝ, 0 < D → Step2Near47.MomentHypCutSharp X E s t D)
    (hmod : ∀ D : ℝ, 0 < D → EntryModulus X E s t D)
    (hmoment : ∀ D : ℝ, 0 < D → ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ ε > (0 : ℝ), ∀ p : ℕ,
      ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      ∀ ws ∈ MomentDuhamelCut.netFinset s t (fun N => ((N : ℝ) + 1) ^ (2 : ℝ)) N,
        ∫ ω, |MomentDuhamelCut.cutTrunc ((N : ℝ) ^ (2 * δ) * 1)
              (Step2FarMart.jSfarSm X E D N ws ω)| ^ (2 * p) ∂B.P
          ≤ C * ((N : ℝ) ^ (ε * p) * (1 : ℝ) ^ (2 * p)))
    (hinit : ∀ D : ℝ, 0 < D → StochDom B.P
      (fun N (_ : Unit) ω => Step2FarMart.jSfarSm X E D N (s N) ω) (fun _ _ _ => (1 : ℝ))) :
    Step45.FlowEq548W X E s t
      (fun N p => Step2FarMart.nearChi (B.W N : ℝ) (B.ell N p.1)
        (zdist (B.L N) (p.2.1 - p.2.2))) :=
  Step2FarMart.flowEq548W_of_entries X hst hs0 ht1 (near_of_sharp X Hy hE hst ht1)
    (aestronglyMeasurable_jSfarSm X E) hmod hmoment hinit

end Assemble

/-! ### 5. The repaired route: the modulus read at `∀ᶠ N`

T232 already built the interface this needs: `RBM.MomentDuhamelCut.CutHypEv` is
`RBM.MomentDuhamelCut.CutHyp` with `modulus` and `mesh_fine` — and only those two — read at
`∀ᶠ N in atTop`, and `RBM.MomentDuhamelCut.stochDom_of_cutHypEv` reproves the conclusion from
it.  `RBM.Step2FarMart.cutHyp_jSfarSm_of_entries` was written against the old `CutHyp`, so the
(5.48) chain inherits the `∀ N` defect; routing it through `CutHypEv` instead removes it, and
nothing else in the chain changes.

`RBM.MomentDuhamelCut.satCutHypEv` together with
`RBM.MomentDuhamelCut.sat_modulus_not_forall` is T232's compiled proof that the weakening is
*strict* (a witness at `Kmod = 1`, `γ = 1/2`, `Θ ≡ 1` that satisfies the `∀ᶠ N` field and fails
the `∀ N` one), so `EntryModulusEv` is not refuted by §3's argument. -/

section Repaired

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E D : ℝ} {s t : ℕ → ℝ}
variable (X : Sample B)

/-- **`RBM.EntryModulus` with `∀ N` replaced by `∀ᶠ N in atTop`** — the only change.  This is
the shape the entrywise modulus of (5.48) has to have; §3 refutes the `∀ N` one. -/
def EntryModulusEv (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) (D : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∀ ω : Ω, ∀ v ∈ Set.Icc (s N) (t N), ∀ w ∈ Set.Icc (s N) (t N),
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

/-- The weakening really is a weakening. -/
theorem entryModulusEv_of_entryModulus (h : EntryModulus X E s t D) :
    EntryModulusEv X E s t D :=
  Filter.Eventually.of_forall fun N ω v hv w hw x => h N ω v hv w hw x

/-- **The `CutHypEv` for `J*^{sm}_{u,D}`**, at the threshold `Θ ≡ 1`.  Field for field
`RBM.Step2FarMart.cutHyp_jSfarSm_of_entries`, with two changes: `meas` is **discharged** by §1
instead of being a hypothesis, and `modulus` is the asymptotic `RBM.EntryModulusEv`.
`window`, `Θ_pos`, `J_nonneg`, `mesh_pos`, `mesh_fine` and `card_le` are proved here exactly as
there, so the `mesh_fine`/`card_le` pair still cannot make the bundle unsatisfiable. -/
noncomputable def cutHypEv_jSfarSm_of_entries
    (hst : ∀ N, s N ≤ t N) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    (hmod : EntryModulusEv X E s t D)
    (hmoment : ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ ε > (0 : ℝ), ∀ p : ℕ, ∃ C > (0 : ℝ),
      ∀ᶠ N : ℕ in atTop,
      ∀ ws ∈ MomentDuhamelCut.netFinset s t (fun N => ((N : ℝ) + 1) ^ (2 : ℝ)) N,
        ∫ ω, |MomentDuhamelCut.cutTrunc ((N : ℝ) ^ (2 * δ) * 1)
              (Step2FarMart.jSfarSm X E D N ws ω)| ^ (2 * p) ∂B.P
          ≤ C * ((N : ℝ) ^ (ε * p) * (1 : ℝ) ^ (2 * p))) :
    MomentDuhamelCut.CutHypEv B.P (fun N u ω => Step2FarMart.jSfarSm X E D N u ω) s t
      (fun _ => 1) where
  window := hst
  δ₀ := 1
  δ₀_pos := one_pos
  Θ_pos := fun _ => one_pos
  J_nonneg := fun _ _ _ => Step2FarMart.jSfarSm_nonneg X
  meas := fun N u => (measurable_jSfarSm X E D N u).aestronglyMeasurable
  mesh := fun N => ((N : ℝ) + 1) ^ (2 : ℝ)
  mesh_pos := fun N => Real.rpow_pos_of_pos (by positivity) _
  Kmod := 1
  γ := 1 / 2
  γ_pos := by norm_num
  modulus := by
    filter_upwards [hmod] with N hN ω v hv w hw
    exact Step2FarMart.abs_jSfarSm_sub_le X fun x =>
      (Step2FarMart.abs_lkFarSm_ratio_sub_le X x).trans (hN ω v hv w hw x)
  mesh_fine := Filter.Eventually.of_forall Step2FarMart.mesh_fine_one_at_sq
  Ccard := 3
  card_le := Step2FarMart.card_le_one_at_sq hs0 ht1
  moment := hmoment

/-- **`J*^{sm}_{u,D} ≺ 1` from the asymptotic interface** — `stochDom_of_cutHypEv` in place of
`stochDom_of_cutHyp`. -/
theorem stochDom_jSfarSm_of_entriesEv
    (hst : ∀ N, s N ≤ t N) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    (hmod : EntryModulusEv X E s t D)
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
  MomentDuhamelCut.stochDom_of_cutHypEv
    (cutHypEv_jSfarSm_of_entries X hst hs0 ht1 hmod hmoment)
    (Filter.Eventually.of_forall fun _ => le_rfl) hinit

/-- **(5.48) at the smooth weight, repaired**: `hmeas` gone (§1), `hnear` from the sharp (5.47)
(§2), and `modulus` at `∀ᶠ N` (§5) instead of the `∀ N` shape that §3 refutes.  The remaining
inputs are exactly `hmoment` (T230/T210) and `hinit` (T241). -/
theorem flowEq548W_of_sharp_entriesEv (hE : |E| < 2)
    (hst : ∀ N, s N ≤ t N) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    (Hy : ∀ D : ℝ, 0 < D → Step2Near47.MomentHypCutSharp X E s t D)
    (hmod : ∀ D : ℝ, 0 < D → EntryModulusEv X E s t D)
    (hmoment : ∀ D : ℝ, 0 < D → ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ ε > (0 : ℝ), ∀ p : ℕ,
      ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      ∀ ws ∈ MomentDuhamelCut.netFinset s t (fun N => ((N : ℝ) + 1) ^ (2 : ℝ)) N,
        ∫ ω, |MomentDuhamelCut.cutTrunc ((N : ℝ) ^ (2 * δ) * 1)
              (Step2FarMart.jSfarSm X E D N ws ω)| ^ (2 * p) ∂B.P
          ≤ C * ((N : ℝ) ^ (ε * p) * (1 : ℝ) ^ (2 * p)))
    (hinit : ∀ D : ℝ, 0 < D → StochDom B.P
      (fun N (_ : Unit) ω => Step2FarMart.jSfarSm X E D N (s N) ω) (fun _ _ _ => (1 : ℝ))) :
    Step45.FlowEq548W X E s t
      (fun N p => Step2FarMart.nearChi (B.W N : ℝ) (B.ell N p.1)
        (zdist (B.L N) (p.2.1 - p.2.2))) :=
  Step2FarMart.flowEq548W_of_jSfarSm X (near_of_sharp X Hy hE hst ht1)
    fun D hD => stochDom_jSfarSm_of_entriesEv X hst hs0 ht1 (hmod D hD) (hmoment D hD)
      (hinit D hD)

end Repaired

/-! ### 6. Satisfiability checks -/

section Sat

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E D : ℝ} {s t : ℕ → ℝ}
variable (X : Sample B)

/-- **§1 is not vacuous.**  `RBM.aestronglyMeasurable_jSfarSm` has no hypotheses, and the
functional it is about is `≥ 1` at *every* sample point — including `ω = 0`, where `H = 0` and
`G = -z⁻¹` — so it is not the measurability of a function that is identically `0`. -/
theorem meas_target_nondegenerate (N : ℕ) (u : ℝ) (ω : Ω) :
    1 ≤ Step2FarMart.jSfarSm X E D N u ω :=
  Step2FarMart.one_le_jSfarSm X

/-- The degenerate witness, transported to the asymptotic field. -/
theorem sat_entryModulusEv_of_window_point (ht : ∀ N, t N = s N) :
    EntryModulusEv X E s t D :=
  entryModulusEv_of_entryModulus X (sat_entryModulus_of_window_point X ht)

end Sat


/-! ### 7. T249: the window that starts at `s ≡ 0`

At `u = 0` the flow is deterministic (`RBM.Sample.H_zero`) and the loop *equals* its primitive
value, which is (2.67) = `RBM.gloop_zero_zt_zero_eq_Kgen`.  So `(L-K)_{0,(+,-),a} = 0` for every
`a` and every `ω`, and `J*^{sm}_{0,D} = 1` identically (`RBM.jSfarSm_zero`).

Consequently, on a window with `s ≡ 0` the field `modulus` of
`RBM.MomentDuhamelCut.CutHypEv` (and the entrywise `RBM.EntryModulusEv`, which implies it)
is **not a modulus of continuity at all**: taking `w = 0` it becomes the *absolute* bound

`J*^{sm}_{v,D}(ω) ≤ 1 + N^{Kmod} v^γ`   for **every** `ω` and every `v ∈ [0, t_N]`,

whose right-hand side tends to `1` as `v → 0`.  `RBM.not_modulusEv_zero_start` turns that into
a refutation as soon as the functional is bounded away from `1` at arbitrarily small positive
times — which is exactly what the unboundedness of the sample does: `ω` is free, so at time `v`
the matrix `H_v = √v X(ω)` ranges over *all* Hermitian matrices, independently of how small `v`
is.  §8 computes the loop for one such matrix. -/

section ZeroStart

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E D : ℝ} {t : ℕ → ℝ}
variable (X : Sample B)

theorem lk_zero (hE : |E| ≤ 2) (N : ℕ) (ω : Ω) (a : LoopArg (B.L N) 2) :
    Step2.lk X E N 0 ω a = 0 := by
  unfold Step2.lk SumZeroDyn.lkT
  have hwf : (LoopData.idx (Step2.sigPM, a)).WF := LoopData.idx_wf _
  have hlen : (LoopData.idx (Step2.sigPM, a)).length = 2 := LoopData.idx_length _
  have h1 : X.Lval E N 0 ω (LoopData.idx (Step2.sigPM, a))
      = B.Kval E N 0 (LoopData.idx (Step2.sigPM, a)) := by
    unfold Sample.Lval Band.Kval
    rw [X.H_zero]
    exact gloop_zero_zt_zero_eq_Kgen hE _ hwf (by omega)
  rw [h1, sub_self]

theorem lkFarSm_zero (hE : |E| ≤ 2) (N : ℕ) (ω : Ω) :
    Step2FarMart.lkFarSm X E N 0 ω = 0 := by
  funext a
  simp [Step2FarMart.lkFarSm, lk_zero X hE N ω a]

theorem jSfarSm_zero (hE : |E| ≤ 2) (N : ℕ) (ω : Ω) :
    Step2FarMart.jSfarSm X E D N 0 ω = 1 := by
  unfold Step2FarMart.jSfarSm Step2.jStar
  rw [lkFarSm_zero X hE N ω]
  simp


/-- The raw `modulus` field of `CutHypEv`, at `s ≡ 0`, for `J*^{sm}`. -/
def ModulusEvAt (X : Sample B) (E D : ℝ) (s t : ℕ → ℝ) (Kmod γ : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∀ ω : Ω, ∀ v ∈ Set.Icc (s N) (t N), ∀ w ∈ Set.Icc (s N) (t N),
    |Step2FarMart.jSfarSm X E D N v ω - Step2FarMart.jSfarSm X E D N w ω|
      ≤ (N : ℝ) ^ Kmod * |v - w| ^ γ

theorem jSfarSm_le_of_modulusEv_zero_start (hE : |E| ≤ 2) {Kmod γ : ℝ}
    (hmod : ModulusEvAt X E D (fun _ => 0) t Kmod γ) :
    ∀ᶠ N : ℕ in atTop, ∀ ω : Ω, ∀ v ∈ Set.Icc (0 : ℝ) (t N),
      Step2FarMart.jSfarSm X E D N v ω ≤ 1 + (N : ℝ) ^ Kmod * v ^ γ := by
  filter_upwards [hmod] with N hN ω v hv
  have h := hN ω v hv 0 ⟨le_rfl, hv.1.trans hv.2⟩
  rw [jSfarSm_zero X hE N ω] at h
  have hv0 : |v - 0| = v := by rw [sub_zero, abs_of_nonneg hv.1]
  rw [hv0] at h
  have := (abs_le.1 h).2
  linarith

theorem not_modulusEv_zero_start (hE : |E| ≤ 2) {Kmod γ : ℝ} (hγ : 0 < γ) {c : ℝ} (hc : 0 < c)
    (hbig : ∀ᶠ N : ℕ in atTop, ∀ v ∈ Set.Ioc (0 : ℝ) (t N), ∃ ω : Ω,
      1 + c ≤ Step2FarMart.jSfarSm X E D N v ω)
    (ht : ∀ᶠ N : ℕ in atTop, 0 < t N) :
    ¬ ModulusEvAt X E D (fun _ => 0) t Kmod γ := by
  intro hmod
  obtain ⟨N, hbound, hbigN, htN⟩ :=
    ((jSfarSm_le_of_modulusEv_zero_start X hE hmod).and (hbig.and ht)).exists
  set K : ℝ := (N : ℝ) ^ Kmod with hK
  have hK0 : 0 ≤ K := Real.rpow_nonneg (Nat.cast_nonneg N) _
  set r : ℝ := (c / (K + 1)) ^ (1 / γ) with hr
  have hcq : 0 < c / (K + 1) := by positivity
  have hr0 : 0 < r := Real.rpow_pos_of_pos hcq _
  have hrγ : r ^ γ = c / (K + 1) := by
    rw [hr, ← Real.rpow_mul hcq.le, one_div, inv_mul_cancel₀ hγ.ne', Real.rpow_one]
  set v : ℝ := min (t N) r with hv
  have hv0 : 0 < v := lt_min htN hr0
  have hvt : v ≤ t N := min_le_left _ _
  obtain ⟨ω, hω⟩ := hbigN v ⟨hv0, hvt⟩
  have hb := hbound ω v ⟨hv0.le, hvt⟩
  have hvγ : v ^ γ ≤ c / (K + 1) := by
    rw [← hrγ]; exact Real.rpow_le_rpow hv0.le (min_le_right _ _) hγ.le
  have hfin : K * v ^ γ ≤ K * (c / (K + 1)) := by
    exact mul_le_mul_of_nonneg_left hvγ hK0
  have hlt : K * (c / (K + 1)) < c := by
    rw [mul_div_assoc']
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  linarith


theorem modulusEvAt_of_entryModulusEv (h : EntryModulusEv X E (fun _ => 0) t D) :
    ModulusEvAt X E D (fun _ => 0) t 1 (1 / 2) := by
  filter_upwards [h] with N hN ω v hv w hw
  exact Step2FarMart.abs_jSfarSm_sub_le X fun x =>
    (Step2FarMart.abs_lkFarSm_ratio_sub_le X x).trans (hN ω v hv w hw x)

theorem not_entryModulusEv_zero_start (hE : |E| ≤ 2) {c : ℝ} (hc : 0 < c)
    (hbig : ∀ᶠ N : ℕ in atTop, ∀ v ∈ Set.Ioc (0 : ℝ) (t N), ∃ ω : Ω,
      1 + c ≤ Step2FarMart.jSfarSm X E D N v ω)
    (ht : ∀ᶠ N : ℕ in atTop, 0 < t N) :
    ¬ EntryModulusEv X E (fun _ => 0) t D := fun h =>
  not_modulusEv_zero_start X hE (by norm_num) hc hbig ht (modulusEvAt_of_entryModulusEv X h)

theorem not_cutHypEv_jSfarSm_zero_start (hE : |E| ≤ 2) {c : ℝ} (hc : 0 < c)
    (hbig : ∀ᶠ N : ℕ in atTop, ∀ v ∈ Set.Ioc (0 : ℝ) (t N), ∃ ω : Ω,
      1 + c ≤ Step2FarMart.jSfarSm X E D N v ω)
    (ht : ∀ᶠ N : ℕ in atTop, 0 < t N) :
    ¬ Nonempty (MomentDuhamelCut.CutHypEv B.P
      (fun N u ω => Step2FarMart.jSfarSm X E D N u ω) (fun _ => 0) t Θ) := by
  rintro ⟨H⟩
  exact not_modulusEv_zero_start X hE H.γ_pos hc hbig ht H.modulus


end ZeroStart

/-! ### 8. T249: the loop really moves, at a fixed spectral parameter

The quantitative half of §7.  `A` is the permutation matrix of an involution `τ`; it is
Hermitian and `A² = 1`, so `(A - z)⁻¹ = (1 - z²)⁻¹(A + z)` in closed form
(`RBM.green_involMat`).  Taking `τ` to be the fibrewise swap of two blocks `a₁ ≠ a₂`
(`RBM.blockSwap`) gives

`L_{(+,-),(a₁,a₂)}(A) = W⁻¹ (1 - z²)⁻¹ (1 - z̄²)⁻¹`,  `L_{(+,-),(a₁,a₂)}(0) = 0`

(`RBM.gloop_pm_involMat`, `RBM.gloop_pm_zero`), at **one and the same** `z`.  So at any fixed
time `v > 0` the far-field loop of the flow `H_v = √v X` takes the two values `0` (at `X = 0`)
and `W⁻¹|1 - z_v²|⁻²` (at `X = v^{-1/2} A`), and the spread `W⁻¹|1 - z_v²|⁻²` does **not**
shrink with `v`.  Divided by `T_{v,D} ≍ W^{-D}` this is the `W^{D-2}` far-field jump. -/

section Involution

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The permutation matrix of an involution `τ`. -/
noncomputable def involMat (τ : n → n) : Matrix n n ℂ :=
  Matrix.of fun i j => if i = τ j then 1 else 0

variable {τ : n → n} (hτ : ∀ i, τ (τ i) = i)

theorem involMat_apply (i j : n) : involMat τ i j = if i = τ j then 1 else 0 := rfl

include hτ in
theorem involMat_symm (i j : n) : (i = τ j) ↔ (j = τ i) := by
  constructor
  · rintro rfl; rw [hτ]
  · rintro rfl; rw [hτ]

include hτ in
theorem involMat_isHermitian : (involMat τ).IsHermitian := by
  ext i j
  show (starRingEnd ℂ) (involMat τ j i) = involMat τ i j
  simp only [involMat_apply]
  by_cases h : i = τ j
  · rw [if_pos h, if_pos ((involMat_symm hτ i j).1 h)]
    simp
  · rw [if_neg h, if_neg (fun hc => h ((involMat_symm hτ i j).2 hc))]
    simp

include hτ in
theorem involMat_mul_self : involMat τ * involMat τ = 1 := by
  ext i k
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (τ k)]
  · simp only [involMat_apply, hτ, Matrix.one_apply]
    simp
  · intro j _ hj
    simp only [involMat_apply]
    rw [if_neg (fun hc => hj hc)]
    ring
  · intro h; exact absurd (Finset.mem_univ _) h

include hτ in
/-- `(A - z)⁻¹ = (1 - z²)⁻¹ (A + z)` for an involution `A`. -/
theorem green_involMat {z : ℂ} (hz : 1 - z ^ 2 ≠ 0) :
    green (involMat τ) z = (1 - z ^ 2)⁻¹ • (involMat τ + z • (1 : Matrix n n ℂ)) := by
  refine Matrix.inv_eq_right_inv ?_
  rw [Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_add,
    involMat_mul_self hτ]
  rw [show (1 : Matrix n n ℂ) + involMat τ * z • (1 : Matrix n n ℂ)
        - (z • (1 : Matrix n n ℂ) * involMat τ + z • (1 : Matrix n n ℂ) * z • (1 : Matrix n n ℂ))
      = (1 - z ^ 2) • (1 : Matrix n n ℂ) by
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.one_mul, Matrix.smul_mul,
      Matrix.one_mul, smul_smul, sub_smul, one_smul, sq]
    abel]
  rw [smul_smul, inv_mul_cancel₀ hz, one_smul]



end Involution

section LoopValue

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- The `(+,-)` two-loop written out: `L_{(+,-),(a₁,a₂)} = W⁻² ∑_{p,q} 1(q ∈ a₁) 1(p ∈ a₂)
G(+)_{pq} G(-)_{qp}`. -/
theorem gloop_pmLoop_eq_sum (H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (z : ℂ) (a₁ a₂ : ZMod L) :
    gloop L W H z (pmLoop a₁ a₂)
      = ∑ p : ZMod L × Fin W, ∑ q : ZMod L × Fin W,
          (if q.1 = a₁ then (W : ℂ)⁻¹ else 0) * (if p.1 = a₂ then (W : ℂ)⁻¹ else 0) *
            (Gsig H z true p q * Gsig H z false q p) := by
  have hprod : gloopProd L W H z (pmLoop a₁ a₂)
      = Gsig H z true * Eblk L W a₁ * (Gsig H z false * Eblk L W a₂) := by
    show Gsig H z true * Eblk L W a₁ * (Gsig H z false * Eblk L W a₂ * 1) = _
    rw [Matrix.mul_one]
  have e1 : ∀ p q, (Gsig H z true * Eblk L W a₁) p q
      = Gsig H z true p q * (if q.1 = a₁ then (W : ℂ)⁻¹ else 0) := by
    intro p q; rw [Eblk, Matrix.mul_diagonal]
  have e2 : ∀ q p, (Gsig H z false * Eblk L W a₂) q p
      = Gsig H z false q p * (if p.1 = a₂ then (W : ℂ)⁻¹ else 0) := by
    intro q p; rw [Eblk, Matrix.mul_diagonal]
  rw [gloop, hprod, Matrix.trace]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [e1, e2]; ring


/-- The fibrewise involution of `ZMod L × Fin W` that swaps the blocks `a₁` and `a₂`. -/
def blockSwap (a₁ a₂ : ZMod L) : ZMod L × Fin W → ZMod L × Fin W :=
  fun j => (a₁ + a₂ - j.1, j.2)

theorem blockSwap_invol (a₁ a₂ : ZMod L) (i : ZMod L × Fin W) :
    blockSwap a₁ a₂ (blockSwap a₁ a₂ i) = i := by
  simp [blockSwap]

@[simp] theorem blockSwap_fst (a₁ a₂ : ZMod L) (j : ZMod L × Fin W) :
    (blockSwap a₁ a₂ j).1 = a₁ + a₂ - j.1 := rfl

theorem gloop_pm_involMat (a₁ a₂ : ZMod L) (ha : a₁ ≠ a₂) {z : ℂ}
    (hz : 1 - z ^ 2 ≠ 0) (hz' : 1 - ((starRingEnd ℂ) z) ^ 2 ≠ 0) :
    gloop L W (involMat (blockSwap a₁ a₂ : ZMod L × Fin W → ZMod L × Fin W)) z
        (pmLoop a₁ a₂)
      = (W : ℂ)⁻¹ * ((1 - z ^ 2)⁻¹ * (1 - ((starRingEnd ℂ) z) ^ 2)⁻¹) := by
  classical
  set τ : ZMod L × Fin W → ZMod L × Fin W := blockSwap a₁ a₂ with hτdef
  have hτ : ∀ i, τ (τ i) = i := blockSwap_invol a₁ a₂
  set c : ℂ := (1 - z ^ 2)⁻¹ * (1 - ((starRingEnd ℂ) z) ^ 2)⁻¹ with hc
  have hGp : ∀ p q, Gsig (involMat τ) z true p q = (1 - z ^ 2)⁻¹ *
      (involMat τ p q + z * (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) p q) := by
    intro p q
    rw [Gsig_true, green_involMat hτ hz]
    rw [Matrix.smul_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
  have hGm : ∀ p q, Gsig (involMat τ) z false p q
      = (1 - ((starRingEnd ℂ) z) ^ 2)⁻¹ * (involMat τ p q + ((starRingEnd ℂ) z) *
          (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) p q) := by
    intro p q
    rw [Gsig_false, green_involMat hτ hz']
    rw [Matrix.smul_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
  have key : ∀ p q : ZMod L × Fin W,
      (if q.1 = a₁ then (W : ℂ)⁻¹ else 0) * (if p.1 = a₂ then (W : ℂ)⁻¹ else 0) *
        (Gsig (involMat τ) z true p q * Gsig (involMat τ) z false q p)
      = (if q.1 = a₁ then (W : ℂ)⁻¹ else 0) * (if p = τ q then (W : ℂ)⁻¹ * c else 0) := by
    intro p q
    by_cases hq : q.1 = a₁
    · by_cases hp : p.1 = a₂
      · have hpq : p ≠ q := by
          intro h; rw [h] at hp; exact ha (hq ▸ hp ▸ rfl)
        have h1 : (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) p q = 0 := by
          simp [Matrix.one_apply, hpq]
        have h2 : (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) q p = 0 := by
          simp [Matrix.one_apply, Ne.symm hpq]
        have h3 : involMat τ q p = involMat τ p q := by
          simp only [involMat_apply]
          by_cases h : p = τ q
          · rw [ite_eq_left ((involMat_symm hτ p q).1 h), ite_eq_left h]
          · rw [ite_eq_right (fun hcc => h ((involMat_symm hτ p q).2 hcc)), ite_eq_right h]
        rw [if_pos hq, if_pos hp, hGp, hGm, h1, h2, h3]
        simp only [involMat_apply]
        by_cases h : p = τ q
        · rw [hc]; simp [h]; ring
        · simp [h]
      · rw [if_neg hp, if_neg (show ¬ p = τ q by
          intro h; apply hp; rw [h, blockSwap_fst, hq]; ring)]
        ring
    · rw [if_neg hq]; ring
  rw [gloop_pmLoop_eq_sum]
  simp only [key]
  rw [Finset.sum_comm]
  have hinner : ∀ q : ZMod L × Fin W,
      (∑ p : ZMod L × Fin W, (if q.1 = a₁ then (W : ℂ)⁻¹ else 0) *
          (if p = τ q then (W : ℂ)⁻¹ * c else 0))
        = (if q.1 = a₁ then (W : ℂ)⁻¹ else 0) * ((W : ℂ)⁻¹ * c) := by
    intro q
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_ite_eq' Finset.univ (τ q) (fun _ => (W : ℂ)⁻¹ * c)]
    simp
  simp only [hinner]
  rw [← Finset.sum_mul]
  have hW0 : ((W : ℂ)) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne W)
  have hcount : (∑ q : ZMod L × Fin W, (if q.1 = a₁ then (W : ℂ)⁻¹ else 0)) = 1 := by
    rw [Fintype.sum_prod_type]
    have hrow : ∀ a : ZMod L, (∑ _α : Fin W, (if a = a₁ then (W : ℂ)⁻¹ else 0))
        = (if a = a₁ then (1 : ℂ) else 0) := by
      intro a
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      split_ifs
      · field_simp
      · ring
    simp only [hrow]
    simp
  rw [hcount, one_mul, hc]


end LoopValue

/-! ### 9. T249 (part B): the `‖X‖`-free Lipschitz bound on `s_N ≥ N^{-C}`
— **moved to `RBM1D/Gauss/LoopLipschitz.lean` (T252)**

The three lemmas of this section (`RBM.isHermitian_real_smul`, `RBM.mul_green_smul`,
`RBM.norm_green_sqrt_sub_le`, `RBM.norm_green_sqrt_sub_le_lip`) are pure resolvent identities
that use nothing from `RBM1D/Flow/`, and `RBM1D/Gauss/` needs them (T252: the loop-level
modulus).  Importing `Flow/` from `Gauss/` would reverse the dependency, so they were sunk to
`RBM1D/Gauss/LoopLipschitz.lean` **with their signatures unchanged**; this file imports it and
the names stay in the `RBM` namespace, so §10 below (the counterexample) is untouched.

The `rfl` probes below are the re-export check: if a signature ever drifts, they fail here. -/

section SqrtFlowLipReexport

open scoped Matrix.Norms.L2Operator

example {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n] {Y : Matrix n n ℂ}
    (hY : Y.IsHermitian) (r : ℝ) : ((r : ℂ) • Y).IsHermitian :=
  isHermitian_real_smul hY r

example {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n] {Y : Matrix n n ℂ}
    (hY : Y.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) {r : ℝ} (hr : r ≠ 0) :
    Y * green ((r : ℂ) • Y) z
      = ((r : ℂ))⁻¹ • ((1 : Matrix n n ℂ) + z • green ((r : ℂ) • Y) z) :=
  mul_green_smul hY hz hr

example {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n] {Y : Matrix n n ℂ}
    (hY : Y.IsHermitian) {E : ℝ} (hE : |E| < 2) {u v : ℝ} (hv0 : 0 < v) (hu0 : 0 ≤ u)
    (hu1 : u < 1) (hv1 : v < 1) :
    ‖green ((Real.sqrt u : ℂ) • Y) (zt E u) - green ((Real.sqrt v : ℂ) • Y) (zt E v)‖
      ≤ |Real.sqrt v - Real.sqrt u| / Real.sqrt v *
          ((etaT E u)⁻¹ * (1 + ‖zt E v‖ * (etaT E v)⁻¹))
        + |u - v| * ((etaT E u)⁻¹ * (etaT E v)⁻¹) :=
  norm_green_sqrt_sub_le hY hE hv0 hu0 hu1 hv1

example {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n] {Y : Matrix n n ℂ}
    (hY : Y.IsHermitian) {E : ℝ} (hE : |E| < 2) {s u v : ℝ} (hs : 0 < s) (hsu : s ≤ u)
    (hsv : s ≤ v) (hu1 : u < 1) (hv1 : v < 1) :
    ‖green ((Real.sqrt u : ℂ) • Y) (zt E u) - green ((Real.sqrt v : ℂ) • Y) (zt E v)‖
      ≤ |u - v| * ((etaT E u)⁻¹ * (1 + ‖zt E v‖ * (etaT E v)⁻¹) / (2 * s)
          + (etaT E u)⁻¹ * (etaT E v)⁻¹) :=
  norm_green_sqrt_sub_le_lip hY hE hs hsu hsv hu1 hv1

end SqrtFlowLipReexport



/-! ### 10. T249: the compiled counterexample on a window that starts at `0`

`RBM.swapSample` is the paper's own flow `H_u = √u X` at the sample point `X = ω A_N`, with
`A_N` the block-swap involution of §8 and `ω : ℝ` free — an unbounded coordinate, as a Gaussian
entry is.  At the time `v > 0` the two sample points `ω = v^{-1/2}` and `ω = 0` give
`H_v = A_N` and `H_v = 0`; the primitive `K_v` is the same for both and cancels, so one of them
has `‖(L-K)_{v,(+,-),(a₁,a₂)}‖ ≥ W⁻¹‖1 - z_v²‖⁻²/2`, **uniformly in `v`**.  Divided by
`T_{v,D} ≤ W⁻²((η_{t₀})⁻² + 1)` this is `≥ 1/(200((η_{t₀})⁻² + 1))`, a constant, while §7 says
the modulus at `s ≡ 0` forces it to be `≤ N^{Kmod} v^γ → 0`.

Hence, **on a non-degenerate window `[0, t_N]` with `t_N ≤ t₀ < 1`**:

* `RBM.not_entryModulusEv_swapSample_of_far` — `RBM.EntryModulusEv` is **false**;
* `RBM.not_cutHypEv_swapSample_of_far` — no `RBM.MomentDuhamelCut.CutHypEv` for `J*^{sm}` exists.

The only geometric input is `hsep`: the two blocks are far enough apart that the smooth far
weight `RBM.Step2FarMart.farChi` is `1` there, i.e. `12 ℓ*_v ≤ ‖a₁ - a₂‖`. -/

section ZeroMat
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem green_zero_eq {z : ℂ} (hz : z ≠ 0) :
    green (0 : Matrix n n ℂ) z = (-z)⁻¹ • (1 : Matrix n n ℂ) := by
  refine Matrix.inv_eq_right_inv ?_
  rw [zero_sub, ← neg_smul, Matrix.smul_mul, Matrix.one_mul, smul_smul,
    mul_inv_cancel₀ (neg_ne_zero.2 hz), one_smul]

end ZeroMat

section ZeroLoop
variable {L W : ℕ} [NeZero L] [NeZero W]

/-- **The `(+,-)` loop of the free resolvent vanishes off the diagonal block.** -/
theorem gloop_pm_zero (a₁ a₂ : ZMod L) (ha : a₁ ≠ a₂) {z : ℂ} (hz : z ≠ 0) :
    gloop L W (0 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) z (pmLoop a₁ a₂) = 0 := by
  rw [gloop_pmLoop_eq_sum]
  refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun q _ => ?_
  by_cases hq : q.1 = a₁
  · by_cases hp : p.1 = a₂
    · have hpq : p ≠ q := by
        intro h; rw [h] at hp; exact ha (hq ▸ hp ▸ rfl)
      have hG : Gsig (0 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) z true p q = 0 := by
        rw [Gsig_true, green_zero_eq hz, Matrix.smul_apply, smul_eq_mul]
        simp [Matrix.one_apply, hpq]
      rw [hG]; ring
    · rw [if_neg hp]; ring
  · rw [if_neg hq]; ring

end ZeroLoop

section BadSample

variable {B : Band ℝ} {E D : ℝ}

/-- **The `√u` flow driven by a block-swap involution.**  `H_u(ω) = √u·ω·A_N` with `A_N` the
permutation matrix of `RBM.blockSwap`; this is the paper's flow `H_u = √u X` at the sample
point `X = ω A_N`, and `ω` is unbounded, exactly as a Gaussian entry is. -/
noncomputable def swapSample (B : Band ℝ) (b : ∀ N, ZMod (B.L N) × ZMod (B.L N)) : Sample B where
  H := fun N u ω => ((Real.sqrt u * ω : ℝ) : ℂ) • involMat (blockSwap (b N).1 (b N).2)
  hermitian := fun N u ω =>
    isHermitian_real_smul (involMat_isHermitian (blockSwap_invol (b N).1 (b N).2)) _
  H_zero := by intro N ω; simp
  measurable := by
    intro N u i j
    simp only [Matrix.smul_apply, smul_eq_mul]
    fun_prop

@[simp] theorem swapSample_H (b : ∀ N, ZMod (B.L N) × ZMod (B.L N)) (N : ℕ) (u ω : ℝ) :
    (swapSample B b).H N u ω
      = ((Real.sqrt u * ω : ℝ) : ℂ) • involMat (blockSwap (b N).1 (b N).2) := rfl

theorem lk_swapSample_eq (b : ∀ N, ZMod (B.L N) × ZMod (B.L N)) (N : ℕ) (v ω : ℝ)
    (a₁ a₂ : ZMod (B.L N)) :
    Step2.lk (swapSample B b) E N v ω ![a₁, a₂]
      = gloop (B.L N) (B.W N) (((Real.sqrt v * ω : ℝ) : ℂ) • involMat (blockSwap (b N).1 (b N).2))
          (zt E v) (pmLoop a₁ a₂) - B.Kval E N v (pmLoop a₁ a₂) := rfl

/-- **The far-field loop of the flow really moves, at every positive time.**

At the time `v > 0` the two sample points `ω = v^{-1/2}` and `ω = 0` give `H_v = A` and
`H_v = 0`, whose `(+,-)` loops at the far pair `((b N).1, (b N).2)` differ by
`W⁻¹(1-z_v²)⁻¹(1-z̄_v²)⁻¹` — a quantity that does **not** shrink as `v → 0`.  The primitive
`K_{v}` is the same for both, so it cancels: one of the two sample points has
`‖(L-K)_v‖ ≥ ‖W⁻¹(1-z_v²)⁻¹(1-z̄_v²)⁻¹‖/2`, and hence `J*^{sm}_{v,D} ≥ 1 + that / (2 T₀)`. -/
theorem exists_jSfarSm_ge_swapSample'
    (b : ∀ N, ZMod (B.L N) × ZMod (B.L N)) (N : ℕ) {v : ℝ} (hv : 0 < v)
    (hne : (b N).1 ≠ (b N).2) (hz0 : zt E v ≠ 0)
    (hz : 1 - (zt E v) ^ 2 ≠ 0) (hz' : 1 - ((starRingEnd ℂ) (zt E v)) ^ 2 ≠ 0)
    (hfar : Step2FarMart.farChi (B.W N : ℝ) (B.ell N v) (zdist (B.L N) ((b N).1 - (b N).2)) = 1)
    {T₀ : ℝ} (_hT₀ : 0 < T₀)
    (hT : tailT (B.W N : ℝ) (B.ell N v) (etaT E v) D
        (zdist (B.L N) ((b N).1 - (b N).2)) ≤ T₀) :
    ∃ ω : ℝ, |ω| ≤ 1 / Real.sqrt v ∧ 1 + ‖((B.W N : ℂ))⁻¹ *
        ((1 - (zt E v) ^ 2)⁻¹ * (1 - ((starRingEnd ℂ) (zt E v)) ^ 2)⁻¹)‖ / (2 * T₀)
      ≤ Step2FarMart.jSfarSm (swapSample B b) E D N v ω := by
  classical
  set a₁ := (b N).1 with ha1
  set a₂ := (b N).2 with ha2
  set aa : LoopArg (B.L N) 2 := ![a₁, a₂] with haa
  set Lv : ℂ := ((B.W N : ℂ))⁻¹ *
    ((1 - (zt E v) ^ 2)⁻¹ * (1 - ((starRingEnd ℂ) (zt E v)) ^ 2)⁻¹) with hLv
  have hW0 : (0 : ℝ) < (B.W N : ℝ) := by exact_mod_cast B.W_pos N
  have hsv : Real.sqrt v ≠ 0 := (Real.sqrt_pos.2 hv).ne'
  have haa0 : aa 0 = a₁ := rfl
  have haa1 : aa 1 = a₂ := rfl
  -- the loop at `ω = v^{-1/2}`
  have h1 : Step2.lk (swapSample B b) E N v (1 / Real.sqrt v) aa
      = Lv - B.Kval E N v (pmLoop a₁ a₂) := by
    rw [haa, lk_swapSample_eq]
    congr 1
    rw [show (Real.sqrt v * (1 / Real.sqrt v) : ℝ) = 1 by field_simp]
    rw [Complex.ofReal_one, one_smul]
    exact gloop_pm_involMat a₁ a₂ hne hz hz'
  -- the loop at `ω = 0`
  have h0 : Step2.lk (swapSample B b) E N v 0 aa
      = 0 - B.Kval E N v (pmLoop a₁ a₂) := by
    rw [haa, lk_swapSample_eq]
    congr 1
    rw [show (Real.sqrt v * 0 : ℝ) = 0 by ring]
    rw [Complex.ofReal_zero, zero_smul]
    exact gloop_pm_zero a₁ a₂ hne hz0
  have hsplit : ‖Lv‖ ≤ ‖Step2.lk (swapSample B b) E N v (1 / Real.sqrt v) aa‖
      + ‖Step2.lk (swapSample B b) E N v 0 aa‖ := by
    have : Lv = Step2.lk (swapSample B b) E N v (1 / Real.sqrt v) aa
        - Step2.lk (swapSample B b) E N v 0 aa := by rw [h1, h0]; ring
    rw [this]
    exact norm_sub_le _ _
  -- one of the two sample points carries half of it
  have hsq0 : (0 : ℝ) ≤ 1 / Real.sqrt v := by positivity
  have hpick : ∃ ω : ℝ, |ω| ≤ 1 / Real.sqrt v ∧
      ‖Lv‖ / 2 ≤ ‖Step2.lk (swapSample B b) E N v ω aa‖ := by
    rcases le_total ‖Step2.lk (swapSample B b) E N v (1 / Real.sqrt v) aa‖
      ‖Step2.lk (swapSample B b) E N v 0 aa‖ with h | h
    · exact ⟨0, by simpa using hsq0, by linarith⟩
    · exact ⟨1 / Real.sqrt v, by rw [abs_of_nonneg hsq0], by linarith⟩
  obtain ⟨ω, hωb, hω⟩ := hpick
  refine ⟨ω, hωb, ?_⟩
  have hTpos : 0 < tailT (B.W N : ℝ) (B.ell N v) (etaT E v) D
      (zdist (B.L N) (aa 0 - aa 1)) := tailT_pos hW0 _
  have hlow := Step2.div_le_jStar_sub_one (L := B.L N)
    (f := Step2FarMart.lkFarSm (swapSample B b) E N v ω) (W := (B.W N : ℝ))
    (ℓu := B.ell N v) (ηu := etaT E v) (D := D) aa
  have hval : Step2FarMart.lkFarSm (swapSample B b) E N v ω aa
      = ‖Step2.lk (swapSample B b) E N v ω aa‖ := by
    rw [Step2FarMart.lkFarSm, haa0, haa1, hfar, one_mul]
  have hnum : ‖Lv‖ / 2 ≤ Step2FarMart.lkFarSm (swapSample B b) E N v ω aa := by
    rw [hval]; exact hω
  have hdiv : ‖Lv‖ / (2 * T₀)
      ≤ Step2FarMart.lkFarSm (swapSample B b) E N v ω aa
        / tailT (B.W N : ℝ) (B.ell N v) (etaT E v) D (zdist (B.L N) (aa 0 - aa 1)) := by
    rw [show ‖Lv‖ / (2 * T₀) = (‖Lv‖ / 2) / T₀ by ring]
    have hT' : tailT (B.W N : ℝ) (B.ell N v) (etaT E v) D
        (zdist (B.L N) (aa 0 - aa 1)) ≤ T₀ := by rw [haa0, haa1]; exact hT
    gcongr
    exact Step2FarMart.lkFarSm_nonneg (swapSample B b) aa
  have := hlow
  unfold Step2FarMart.jSfarSm
  linarith [hdiv, hlow]

/-- **T249's witness, without the bound on it.**  Signature unchanged; the proof is now the
projection of `RBM.exists_jSfarSm_ge_swapSample'`, which also records that the witness lies in
`{|ω| ≤ v^{-1/2}}` — the datum T256's event argument (`RBM.t249_witness_norm_gt`) needs and
could not extract from the bare existential. -/
theorem exists_jSfarSm_ge_swapSample
    (b : ∀ N, ZMod (B.L N) × ZMod (B.L N)) (N : ℕ) {v : ℝ} (hv : 0 < v)
    (hne : (b N).1 ≠ (b N).2) (hz0 : zt E v ≠ 0)
    (hz : 1 - (zt E v) ^ 2 ≠ 0) (hz' : 1 - ((starRingEnd ℂ) (zt E v)) ^ 2 ≠ 0)
    (hfar : Step2FarMart.farChi (B.W N : ℝ) (B.ell N v) (zdist (B.L N) ((b N).1 - (b N).2)) = 1)
    {T₀ : ℝ} (hT₀ : 0 < T₀)
    (hT : tailT (B.W N : ℝ) (B.ell N v) (etaT E v) D
        (zdist (B.L N) ((b N).1 - (b N).2)) ≤ T₀) :
    ∃ ω : ℝ, 1 + ‖((B.W N : ℂ))⁻¹ *
        ((1 - (zt E v) ^ 2)⁻¹ * (1 - ((starRingEnd ℂ) (zt E v)) ^ 2)⁻¹)‖ / (2 * T₀)
      ≤ Step2FarMart.jSfarSm (swapSample B b) E D N v ω :=
  (exists_jSfarSm_ge_swapSample' b N hv hne hz0 hz hz' hfar hT₀ hT).imp fun _ h => h.2

/-- The spectral parameter of the flow is off the real axis, so neither `z_v` nor `z_v² - 1`
nor `z̄_v² - 1` vanishes. -/
theorem zt_ne_zero_and_sq {E v : ℝ} (hE : |E| < 2) (hv : v < 1) :
    zt E v ≠ 0 ∧ 1 - (zt E v) ^ 2 ≠ 0 ∧ 1 - ((starRingEnd ℂ) (zt E v)) ^ 2 ≠ 0 := by
  have hη : 0 < etaT E v := by
    show 0 < (1 - v) * (mE E).im; exact mul_pos (by linarith) (mE_im_pos hE)
  have him : (zt E v).im ≠ 0 := by rw [← etaT_eq_zt_im]; exact hη.ne'
  have hsq : ∀ w : ℂ, w.im ≠ 0 → 1 - w ^ 2 ≠ 0 := by
    intro w hw h
    have : (w - 1) * (w + 1) = 0 := by linear_combination -h
    rcases mul_eq_zero.1 this with h1 | h1
    · exact hw (by rw [sub_eq_zero] at h1; rw [h1]; simp)
    · exact hw (by rw [add_eq_zero_iff_eq_neg] at h1; rw [h1]; simp)
  refine ⟨fun h => him (by rw [h]; simp), hsq _ him, hsq _ ?_⟩
  simpa using him

/-- **`EntryModulusEv` fails on a non-degenerate window `[0, t_N]`** for the flow
`H_u = √u ω A_N`: the entrywise modulus of (5.48) has no producer there.  The hypothesis
`hgap` is pure scalar arithmetic — `W ≥ 1`, `ℓ_v ≥ 1`, `η_v ≥ η_{t₀}`, `‖z_v‖ ≤ 3` give
`‖L_v‖/(2T_{v,D}) ≥ W/(400(η_{t₀}⁻² + 1))` for `D ≥ 2`. -/
theorem hbig_swapSample {t : ℕ → ℝ}
    (b : ∀ N, ZMod (B.L N) × ZMod (B.L N)) (hE : |E| < 2) {c : ℝ}
    (ht1 : ∀ᶠ N : ℕ in atTop, t N < 1)
    (hgap : ∀ᶠ N : ℕ in atTop, ∀ v ∈ Set.Ioc (0 : ℝ) (t N),
        (b N).1 ≠ (b N).2 ∧
        Step2FarMart.farChi (B.W N : ℝ) (B.ell N v) (zdist (B.L N) ((b N).1 - (b N).2)) = 1 ∧
        c ≤ ‖((B.W N : ℂ))⁻¹ *
              ((1 - (zt E v) ^ 2)⁻¹ * (1 - ((starRingEnd ℂ) (zt E v)) ^ 2)⁻¹)‖
            / (2 * tailT (B.W N : ℝ) (B.ell N v) (etaT E v) D
                (zdist (B.L N) ((b N).1 - (b N).2)))) :
    ∀ᶠ N : ℕ in atTop, ∀ v ∈ Set.Ioc (0 : ℝ) (t N), ∃ ω : ℝ,
      1 + c ≤ Step2FarMart.jSfarSm (swapSample B b) E D N v ω := by
  filter_upwards [hgap, ht1] with N hN hN1 v hv
  obtain ⟨hne, hfar, hcle⟩ := hN v hv
  have hW0 : (0 : ℝ) < (B.W N : ℝ) := by exact_mod_cast B.W_pos N
  obtain ⟨hz0, hz, hz'⟩ := zt_ne_zero_and_sq (E := E) (v := v) hE (lt_of_le_of_lt hv.2 hN1)
  obtain ⟨ω, hω⟩ := exists_jSfarSm_ge_swapSample (E := E) (D := D) b N hv.1 hne hz0 hz hz' hfar
    (T₀ := tailT (B.W N : ℝ) (B.ell N v) (etaT E v) D
      (zdist (B.L N) ((b N).1 - (b N).2))) (tailT_pos hW0 _) le_rfl
  exact ⟨ω, le_trans (by linarith) hω⟩

end BadSample

section Gap
variable {B : Band ℝ} {E D : ℝ}

theorem norm_zt_le_three_of_mem {E v : ℝ} (hE : |E| ≤ 2) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    ‖zt E v‖ ≤ 3 := by
  have hz : zt E v = (E : ℂ) + ((1 - v : ℝ) : ℂ) * mE E := by
    rw [zt]; push_cast; ring
  rw [hz]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    norm_mE hE, mul_one, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - v)]
  linarith

theorem norm_one_sub_sq_le {E v : ℝ} (hE : |E| < 2) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    ‖1 - (zt E v) ^ 2‖ ≤ 10 := by
  have h := norm_zt_le_three_of_mem (E := E) (v := v) hE.le hv0 hv1
  refine (norm_sub_le _ _).trans ?_
  rw [norm_one, norm_pow]
  nlinarith [norm_nonneg (zt E v)]

/-- The lower bound on the far-field spread that `hgap` of
`RBM.not_entryModulusEv_swapSample` asks for. -/
theorem gap_lower_mul_W {E v D : ℝ} (hE : |E| < 2) {W L : ℕ} (hW : 1 ≤ W) (hL : 3 ≤ L)
    (hv0 : 0 < v) {t₀ : ℝ} (hvt : v ≤ t₀) (ht₀ : t₀ < 1) (hD : 2 ≤ D) (d : ℝ) :
    (W : ℝ) / (200 * ((etaT E t₀)⁻¹ ^ 2 + 1))
      ≤ ‖((W : ℂ))⁻¹ * ((1 - (zt E v) ^ 2)⁻¹ * (1 - ((starRingEnd ℂ) (zt E v)) ^ 2)⁻¹)‖
        / (2 * tailT (W : ℝ) (ellHat L (v : ℂ)) (etaT E v) D d) := by
  have : NeZero L := ⟨by omega⟩
  have hv1 : v < 1 := lt_of_le_of_lt hvt ht₀
  have hWR : (1 : ℝ) ≤ (W : ℝ) := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < (W : ℝ) := by linarith
  have hηv : 0 < etaT E v := by
    show 0 < (1 - v) * (mE E).im; exact mul_pos (by linarith) (mE_im_pos hE)
  have hηt : 0 < etaT E t₀ := by
    show 0 < (1 - t₀) * (mE E).im; exact mul_pos (by linarith) (mE_im_pos hE)
  have hηle : etaT E t₀ ≤ etaT E v := Gauss.etaT_le_of_le hE hvt
  have hℓ : (1 : ℝ) ≤ ellHat L (v : ℂ) := one_le_ellHat L hL hv0.le hv1
  obtain ⟨hz0, hz, hz'⟩ := zt_ne_zero_and_sq (E := E) (v := v) hE hv1
  -- the numerator
  have hcj : ‖1 - ((starRingEnd ℂ) (zt E v)) ^ 2‖ = ‖1 - (zt E v) ^ 2‖ := by
    rw [show (1 : ℂ) - ((starRingEnd ℂ) (zt E v)) ^ 2
        = (starRingEnd ℂ) (1 - (zt E v) ^ 2) by simp]
    exact RCLike.norm_conj _
  have hnsq := norm_one_sub_sq_le (E := E) (v := v) hE hv0.le hv1.le
  have hnsq0 : 0 < ‖1 - (zt E v) ^ 2‖ := norm_pos_iff.2 hz
  have hnumeq : ‖((W : ℂ))⁻¹ * ((1 - (zt E v) ^ 2)⁻¹ * (1 - ((starRingEnd ℂ) (zt E v)) ^ 2)⁻¹)‖
      = ((W : ℝ) * (‖1 - (zt E v) ^ 2‖ * ‖1 - (zt E v) ^ 2‖))⁻¹ := by
    rw [norm_mul, norm_mul, norm_inv, norm_inv, norm_inv, hcj, Complex.norm_natCast]
    field_simp
  have hnum : 1 / (100 * (W : ℝ))
      ≤ ‖((W : ℂ))⁻¹ * ((1 - (zt E v) ^ 2)⁻¹ * (1 - ((starRingEnd ℂ) (zt E v)) ^ 2)⁻¹)‖ := by
    rw [hnumeq, ← one_div]
    refine one_div_le_one_div_of_le (by positivity) ?_
    have hsq : ‖1 - (zt E v) ^ 2‖ * ‖1 - (zt E v) ^ 2‖ ≤ 100 := by nlinarith
    nlinarith [hsq, hWR, hnsq0]
  -- the denominator
  have hexp : Real.exp (-Real.sqrt (d / ellHat L (v : ℂ))) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    simpa using Real.sqrt_nonneg (d / ellHat L (v : ℂ))
  have hWD : (W : ℝ) ^ (-D) ≤ ((W : ℝ) ^ 2)⁻¹ := by
    have h2 : ((W : ℝ) ^ 2)⁻¹ = (W : ℝ) ^ (-(2 : ℝ)) := by
      rw [Real.rpow_neg hW0.le, ← Real.rpow_natCast (W : ℝ) 2]
      norm_num
    rw [h2]
    exact Real.rpow_le_rpow_of_exponent_le hWR (by linarith)
  have hfirst : (((W : ℝ) * ellHat L (v : ℂ) * etaT E v) ^ 2)⁻¹ *
        Real.exp (-Real.sqrt (d / ellHat L (v : ℂ)))
      ≤ ((W : ℝ) ^ 2)⁻¹ * (etaT E t₀)⁻¹ ^ 2 := by
    have hpos : (0 : ℝ) < ((W : ℝ) * ellHat L (v : ℂ) * etaT E v) ^ 2 := by positivity
    have hℓη : etaT E t₀ ≤ ellHat L (v : ℂ) * etaT E v := by
      nlinarith [mul_le_mul_of_nonneg_right hℓ hηv.le]
    have hx : (W : ℝ) * etaT E t₀ ≤ (W : ℝ) * ellHat L (v : ℂ) * etaT E v := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hℓη hW0.le
    have hb : ((W : ℝ) ^ 2) * (etaT E t₀) ^ 2
        ≤ ((W : ℝ) * ellHat L (v : ℂ) * etaT E v) ^ 2 := by
      have h0 : (0 : ℝ) ≤ (W : ℝ) * etaT E t₀ := by positivity
      have hp := pow_le_pow_left₀ h0 hx 2
      nlinarith [hp]
    have h1 : (((W : ℝ) * ellHat L (v : ℂ) * etaT E v) ^ 2)⁻¹
        ≤ (((W : ℝ) ^ 2) * (etaT E t₀) ^ 2)⁻¹ := by
      rw [← one_div, ← one_div]
      exact one_div_le_one_div_of_le (by positivity) hb
    have h2 : (((W : ℝ) ^ 2) * (etaT E t₀) ^ 2)⁻¹ = ((W : ℝ) ^ 2)⁻¹ * (etaT E t₀)⁻¹ ^ 2 := by
      field_simp
    calc (((W : ℝ) * ellHat L (v : ℂ) * etaT E v) ^ 2)⁻¹ *
          Real.exp (-Real.sqrt (d / ellHat L (v : ℂ)))
        ≤ (((W : ℝ) * ellHat L (v : ℂ) * etaT E v) ^ 2)⁻¹ * 1 := by
          exact mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = (((W : ℝ) * ellHat L (v : ℂ) * etaT E v) ^ 2)⁻¹ := mul_one _
      _ ≤ (((W : ℝ) ^ 2) * (etaT E t₀) ^ 2)⁻¹ := h1
      _ = ((W : ℝ) ^ 2)⁻¹ * (etaT E t₀)⁻¹ ^ 2 := h2
  have hden : tailT (W : ℝ) (ellHat L (v : ℂ)) (etaT E v) D d
      ≤ ((W : ℝ) ^ 2)⁻¹ * ((etaT E t₀)⁻¹ ^ 2 + 1) := by
    rw [tailT]
    have : ((W : ℝ) ^ 2)⁻¹ * ((etaT E t₀)⁻¹ ^ 2 + 1)
        = ((W : ℝ) ^ 2)⁻¹ * (etaT E t₀)⁻¹ ^ 2 + ((W : ℝ) ^ 2)⁻¹ := by ring
    rw [this]
    exact add_le_add hfirst hWD
  have hTpos : 0 < tailT (W : ℝ) (ellHat L (v : ℂ)) (etaT E v) D d := tailT_pos hW0 _
  have hc1 : (0 : ℝ) < (etaT E t₀)⁻¹ ^ 2 + 1 := by positivity
  have hkey : (1 / (100 * (W : ℝ))) / (2 * (((W : ℝ) ^ 2)⁻¹ * ((etaT E t₀)⁻¹ ^ 2 + 1)))
      = (W : ℝ) / (200 * ((etaT E t₀)⁻¹ ^ 2 + 1)) := by
    field_simp
    ring
  calc (W : ℝ) / (200 * ((etaT E t₀)⁻¹ ^ 2 + 1))
      = (1 / (100 * (W : ℝ))) / (2 * (((W : ℝ) ^ 2)⁻¹ * ((etaT E t₀)⁻¹ ^ 2 + 1))) := hkey.symm
    _ ≤ ‖((W : ℂ))⁻¹ * ((1 - (zt E v) ^ 2)⁻¹ * (1 - ((starRingEnd ℂ) (zt E v)) ^ 2)⁻¹)‖
          / (2 * tailT (W : ℝ) (ellHat L (v : ℂ)) (etaT E v) D d) := by
        gcongr

/-- **T249's constant `c`**, i.e. `RBM.gap_lower_mul_W` with the factor `W ≥ 1` discarded.
Signature unchanged; keeping the `W` (which is what `RBM.gap_lower_mul_W` does) is what §13
needs, because a *diverging* jump is what refutes the modulus on the event. -/
theorem gap_lower {E v D : ℝ} (hE : |E| < 2) {W L : ℕ} (hW : 1 ≤ W) (hL : 3 ≤ L)
    (hv0 : 0 < v) {t₀ : ℝ} (hvt : v ≤ t₀) (ht₀ : t₀ < 1) (hD : 2 ≤ D) (d : ℝ) :
    1 / (200 * ((etaT E t₀)⁻¹ ^ 2 + 1))
      ≤ ‖((W : ℂ))⁻¹ * ((1 - (zt E v) ^ 2)⁻¹ * (1 - ((starRingEnd ℂ) (zt E v)) ^ 2)⁻¹)‖
        / (2 * tailT (W : ℝ) (ellHat L (v : ℂ)) (etaT E v) D d) := by
  refine le_trans ?_ (gap_lower_mul_W hE hW hL hv0 hvt ht₀ hD d)
  have hWR : (1 : ℝ) ≤ (W : ℝ) := by exact_mod_cast hW
  have hc1 : (0 : ℝ) < 200 * ((etaT E t₀)⁻¹ ^ 2 + 1) := by positivity
  gcongr

/-- **The verdict of T249(甲): `RBM.EntryModulusEv` is false on a non-degenerate window
`[0, t_N]` with `t_N ≤ t₀ < 1`**, for the flow `H_u = √u ω A_N` and any `D ≥ 2`, as soon as the
two blocks `b N` are far enough apart for the smooth far weight to be `1`.  No `hgap`, no free
constant: `c = 1/(200((η_{t₀})⁻² + 1))`. -/
theorem not_entryModulusEv_swapSample_of_far {t : ℕ → ℝ} {t₀ : ℝ}
    (b : ∀ N, ZMod (B.L N) × ZMod (B.L N)) (hE : |E| < 2) (hD : 2 ≤ D) (ht₀ : t₀ < 1)
    (ht0 : ∀ᶠ N : ℕ in atTop, 0 < t N) (htt : ∀ᶠ N : ℕ in atTop, t N ≤ t₀)
    (hsep : ∀ᶠ N : ℕ in atTop, (b N).1 ≠ (b N).2 ∧ ∀ v ∈ Set.Ioc (0 : ℝ) (t N),
        Step2FarMart.farChi (B.W N : ℝ) (B.ell N v) (zdist (B.L N) ((b N).1 - (b N).2)) = 1) :
    ¬ EntryModulusEv (swapSample B b) E (fun _ => 0) t D := by
  refine not_entryModulusEv_zero_start (swapSample B b) hE.le
    (c := 1 / (200 * ((etaT E t₀)⁻¹ ^ 2 + 1))) (by positivity)
    (hbig_swapSample b hE ?_ ?_) ht0
  · filter_upwards [htt] with N h using lt_of_le_of_lt h ht₀
  · filter_upwards [hsep, htt] with N hsepN hle v hv
    exact ⟨hsepN.1, hsepN.2 v hv,
      gap_lower hE (B.W_pos N) (B.three_le_L N) hv.1 (hv.2.trans hle) ht₀ hD _⟩

/-- The same verdict in the structural form of T232's `RBM.MomentDuhamelCut.sat_no_cutHyp`:
**no `CutHypEv` for `J*^{sm}_{·,D}` exists on a window that starts at `0`.** -/
theorem not_cutHypEv_swapSample_of_far {t Θ : ℕ → ℝ} {t₀ : ℝ}
    (b : ∀ N, ZMod (B.L N) × ZMod (B.L N)) (hE : |E| < 2) (hD : 2 ≤ D) (ht₀ : t₀ < 1)
    (ht0 : ∀ᶠ N : ℕ in atTop, 0 < t N) (htt : ∀ᶠ N : ℕ in atTop, t N ≤ t₀)
    (hsep : ∀ᶠ N : ℕ in atTop, (b N).1 ≠ (b N).2 ∧ ∀ v ∈ Set.Ioc (0 : ℝ) (t N),
        Step2FarMart.farChi (B.W N : ℝ) (B.ell N v) (zdist (B.L N) ((b N).1 - (b N).2)) = 1) :
    ¬ Nonempty (MomentDuhamelCut.CutHypEv B.P
      (fun N u ω => Step2FarMart.jSfarSm (swapSample B b) E D N u ω) (fun _ => 0) t Θ) := by
  refine not_cutHypEv_jSfarSm_zero_start (swapSample B b) hE.le
    (c := 1 / (200 * ((etaT E t₀)⁻¹ ^ 2 + 1))) (by positivity)
    (hbig_swapSample b hE ?_ ?_) ht0
  · filter_upwards [htt] with N h using lt_of_le_of_lt h ht₀
  · filter_upwards [hsep, htt] with N hsepN hle v hv
    exact ⟨hsepN.1, hsepN.2 v hv,
      gap_lower hE (B.W_pos N) (B.three_le_L N) hv.1 (hv.2.trans hle) ht₀ hD _⟩

end Gap


/-! ### 11. T258(甲): the modulus with its exponents `(Kmod, γ)` as parameters

`RBM.EntryModulusEv` hard-codes `(N : ℝ)^1 * |v - w|^{1/2}` inside the `def`, i.e. the pair
`(Kmod, γ) = (1, 1/2)`.  T252 showed that **nobody can produce it**: the honest loop-level
Lipschitz constant is `N^{1+C+D} |v - w|^1` (`RBM.norm_lk_sub_le_lip`), which on a window of
width `≥ N^{-C}` is *not* `≤ N^1 |v - w|^{1/2}`; and T256's `RBM.kmod_ge_of_jump` shows that even
the event-restricted field forces `Kmod` to grow linearly in `D`.  So the pair has to travel
with the statement.

`RBM.EntryModulusEvK` is `RBM.EntryModulusEv` with the two exponents abstracted; at `(1, 1/2)`
the two are the *same proposition*, by `rfl` (`RBM.entryModulusEvK_one_half`).  The old name,
its body, and every downstream consumer are left untouched.

`γ` is always carried with `0 < γ`: at `γ = 0` the right-hand side is `N^{Kmod} * 1`, an
absolute bound rather than a modulus, and the field would say nothing about continuity.  `Kmod`
is a real *parameter of the statement*, never a function of the quantity being estimated.

The mesh cannot stay at `(N+1)²` once `Kmod` moves: `RBM.MomentDuhamelCut.CutHypEv.mesh_fine`
asks `N^{Kmod} (1/m_N)^γ ≤ Θ_N`.  `RBM.meshK` is the mesh that works for every admissible pair,
`m_N = (N+1)^{Kmod/γ}`, and `RBM.meshK_one_half` is the check that at `(1, 1/2)` it is exactly
the old `(N+1)²`, with `Ccard = Kmod/γ + 1 = 3`. -/

section Parametric

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E D : ℝ} {s t : ℕ → ℝ}
variable (X : Sample B)

/-- **`RBM.EntryModulusEv` with its two exponents as parameters.**  Body for body
`RBM.EntryModulusEv`; the single change is `(N : ℝ) ^ (1 : ℝ) * |v - w| ^ ((1 : ℝ)/2)` ⤳
`(N : ℝ) ^ Kmod * |v - w| ^ γ`. -/
def EntryModulusEvK (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) (D Kmod γ : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∀ ω : Ω, ∀ v ∈ Set.Icc (s N) (t N), ∀ w ∈ Set.Icc (s N) (t N),
    ∀ x : LoopArg (B.L N) 2,
      15 / 8 * |(zdist (B.L N) (x 0 - x 1) : ℝ) / (6 * ellStar (B.W N : ℝ) (B.ell N v))
            - (zdist (B.L N) (x 0 - x 1) : ℝ) / (6 * ellStar (B.W N : ℝ) (B.ell N w))|
          * |‖Step2.lk X E N v ω x‖ / tailT (B.W N : ℝ) (B.ell N v) (etaT E v) D
              (zdist (B.L N) (x 0 - x 1))|
        + |‖Step2.lk X E N v ω x‖ / tailT (B.W N : ℝ) (B.ell N v) (etaT E v) D
              (zdist (B.L N) (x 0 - x 1))
            - ‖Step2.lk X E N w ω x‖ / tailT (B.W N : ℝ) (B.ell N w) (etaT E w) D
              (zdist (B.L N) (x 0 - x 1))|
          ≤ (N : ℝ) ^ Kmod * |v - w| ^ γ

/-- **The certificate that the parametrization is conservative**: at `(Kmod, γ) = (1, 1/2)` the
parametric field is *the same proposition* as `RBM.EntryModulusEv` — `Iff.rfl`, not a proof. -/
theorem entryModulusEvK_one_half :
    EntryModulusEvK X E s t D 1 (1 / 2) ↔ EntryModulusEv X E s t D := Iff.rfl

theorem entryModulusEvK_of_entryModulusEv (h : EntryModulusEv X E s t D) :
    EntryModulusEvK X E s t D 1 (1 / 2) := h

theorem entryModulusEv_of_entryModulusEvK (h : EntryModulusEvK X E s t D 1 (1 / 2)) :
    EntryModulusEv X E s t D := h

/-- **The mesh that matches the pair `(Kmod, γ)`**: `m_N = (N+1)^{Kmod/γ}`.  At `(1, 1/2)` this
is the `(N+1)²` of `RBM.Step2FarMart.mesh_fine_one_at_sq`. -/
noncomputable def meshK (Kmod γ : ℝ) : ℕ → ℝ := fun N => ((N : ℝ) + 1) ^ (Kmod / γ)

theorem meshK_pos (Kmod γ : ℝ) (N : ℕ) : 0 < meshK Kmod γ N :=
  Real.rpow_pos_of_pos (by positivity) _

/-- At the flow's own pair the mesh is the old one, byte for byte. -/
theorem meshK_one_half : meshK 1 (1 / 2) = fun N : ℕ => ((N : ℝ) + 1) ^ (2 : ℝ) := by
  funext N
  norm_num [meshK]

/-- `Ccard` at the flow's own pair is the old `3`. -/
theorem ccardK_one_half : (1 : ℝ) / (1 / 2) + 1 = 3 := by norm_num

/-- **`mesh_fine` at `RBM.meshK`**, for every admissible pair: `N^{Kmod} (1/m_N)^γ ≤ 1`. -/
theorem mesh_fine_at_meshK {Kmod γ : ℝ} (hK : 0 ≤ Kmod) (hγ : 0 < γ) (N : ℕ) :
    (N : ℝ) ^ Kmod * (1 / meshK Kmod γ N) ^ γ ≤ 1 := by
  have ha : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have h1 : (1 / meshK Kmod γ N) = ((N : ℝ) + 1) ^ (-(Kmod / γ)) := by
    rw [meshK, Real.rpow_neg ha.le, one_div]
  rw [h1, ← Real.rpow_mul ha.le]
  have h2 : (-(Kmod / γ)) * γ = -Kmod := by field_simp
  rw [h2]
  have h3 : (N : ℝ) ^ Kmod ≤ ((N : ℝ) + 1) ^ Kmod :=
    Real.rpow_le_rpow (Nat.cast_nonneg N) (by linarith) hK
  have h4 : (0 : ℝ) < ((N : ℝ) + 1) ^ (-Kmod) := Real.rpow_pos_of_pos ha _
  calc (N : ℝ) ^ Kmod * ((N : ℝ) + 1) ^ (-Kmod)
      ≤ ((N : ℝ) + 1) ^ Kmod * ((N : ℝ) + 1) ^ (-Kmod) :=
        mul_le_mul_of_nonneg_right h3 h4.le
    _ = 1 := by rw [← Real.rpow_add ha]; simp

/-- **`card_le` at the same mesh**, with `Ccard = Kmod/γ + 1`: the window has length `< 1`, so
the net has at most `(N+1)^{Kmod/γ} + 2 ≤ N^{Kmod/γ + 1}` points once `N ≥ max(4, 2^{Kmod/γ+1})`.
Together with `RBM.mesh_fine_at_meshK` this settles, at *one* mesh and by theorems, the pair of
fields that pull in opposite directions. -/
theorem card_le_at_meshK {Kmod γ : ℝ} (hK : 0 ≤ Kmod) (hγ : 0 < γ)
    (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1) :
    ∀ᶠ N : ℕ in atTop,
      (t N - s N) * meshK Kmod γ N + 2 ≤ (N : ℝ) ^ (Kmod / γ + 1) := by
  set a : ℝ := Kmod / γ with hadef
  have ha0 : 0 ≤ a := div_nonneg hK hγ.le
  filter_upwards [eventually_ge_atTop (max 4 ⌈(2 : ℝ) ^ (a + 1)⌉₊)] with N hN
  have hN4 : 4 ≤ N := le_trans (le_max_left _ _) hN
  have hNc : ⌈(2 : ℝ) ^ (a + 1)⌉₊ ≤ N := le_trans (le_max_right _ _) hN
  have hx4 : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN4
  have hx0 : (0 : ℝ) < (N : ℝ) := by linarith
  have h2a : (2 : ℝ) ^ (a + 1) ≤ (N : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hNc)
  have hsplit : (2 : ℝ) ^ (a + 1) = 2 * (2 : ℝ) ^ a := by
    rw [Real.rpow_add (by norm_num), Real.rpow_one]; ring
  have h2a' : (2 : ℝ) ^ a ≤ (N : ℝ) / 2 := by rw [hsplit] at h2a; linarith
  have hb : ((N : ℝ) + 1) ^ a ≤ (2 * (N : ℝ)) ^ a :=
    Real.rpow_le_rpow (by positivity) (by linarith) ha0
  have hmul : (2 * (N : ℝ)) ^ a = (2 : ℝ) ^ a * (N : ℝ) ^ a :=
    Real.mul_rpow (by norm_num) hx0.le
  have hxa1 : (1 : ℝ) ≤ (N : ℝ) ^ a := Real.one_le_rpow (by linarith) ha0
  have hxa0 : (0 : ℝ) < (N : ℝ) ^ a := by linarith
  have hts : t N - s N ≤ 1 := by linarith [hs0 N, ht1 N]
  have hmeshnn : (0 : ℝ) ≤ meshK Kmod γ N := (meshK_pos Kmod γ N).le
  have hstep1 : (t N - s N) * meshK Kmod γ N ≤ ((N : ℝ) + 1) ^ a := by
    have := mul_le_mul_of_nonneg_right hts hmeshnn
    simpa [meshK, hadef, one_mul] using this
  have hstep2 : ((N : ℝ) + 1) ^ a ≤ ((N : ℝ) / 2) * (N : ℝ) ^ a := by
    refine le_trans hb ?_
    rw [hmul]
    exact mul_le_mul_of_nonneg_right h2a' hxa0.le
  have hstep3 : (2 : ℝ) ≤ ((N : ℝ) / 2) * (N : ℝ) ^ a := by nlinarith
  have hfin : (N : ℝ) ^ (a + 1) = (N : ℝ) ^ a * (N : ℝ) := by
    rw [Real.rpow_add hx0, Real.rpow_one]
  rw [hfin]
  nlinarith [hstep1, hstep2, hstep3]

/-- **The `CutHypEv` for `J*^{sm}_{u,D}` at an arbitrary admissible pair `(Kmod, γ)`.**  Field
for field `RBM.cutHypEv_jSfarSm_of_entries`, with the two exponents, the mesh and `Ccard` all
moving together.  At `(1, 1/2)` the mesh is `(N+1)²` (`RBM.meshK_one_half`) and `Ccard` is `3`
(`RBM.ccardK_one_half`), i.e. exactly the old bundle. -/
noncomputable def cutHypEv_jSfarSm_of_entriesK {Kmod γ : ℝ} (hK : 0 ≤ Kmod) (hγ : 0 < γ)
    (hst : ∀ N, s N ≤ t N) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    (hmod : EntryModulusEvK X E s t D Kmod γ)
    (hmoment : ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ ε > (0 : ℝ), ∀ p : ℕ, ∃ C > (0 : ℝ),
      ∀ᶠ N : ℕ in atTop,
      ∀ ws ∈ MomentDuhamelCut.netFinset s t (meshK Kmod γ) N,
        ∫ ω, |MomentDuhamelCut.cutTrunc ((N : ℝ) ^ (2 * δ) * 1)
              (Step2FarMart.jSfarSm X E D N ws ω)| ^ (2 * p) ∂B.P
          ≤ C * ((N : ℝ) ^ (ε * p) * (1 : ℝ) ^ (2 * p))) :
    MomentDuhamelCut.CutHypEv B.P (fun N u ω => Step2FarMart.jSfarSm X E D N u ω) s t
      (fun _ => 1) where
  window := hst
  δ₀ := 1
  δ₀_pos := one_pos
  Θ_pos := fun _ => one_pos
  J_nonneg := fun _ _ _ => Step2FarMart.jSfarSm_nonneg X
  meas := fun N u => (measurable_jSfarSm X E D N u).aestronglyMeasurable
  mesh := meshK Kmod γ
  mesh_pos := meshK_pos Kmod γ
  Kmod := Kmod
  γ := γ
  γ_pos := hγ
  modulus := by
    filter_upwards [hmod] with N hN ω v hv w hw
    exact Step2FarMart.abs_jSfarSm_sub_le X fun x =>
      (Step2FarMart.abs_lkFarSm_ratio_sub_le X x).trans (hN ω v hv w hw x)
  mesh_fine := Filter.Eventually.of_forall (mesh_fine_at_meshK hK hγ)
  Ccard := Kmod / γ + 1
  card_le := card_le_at_meshK hK hγ hs0 ht1
  moment := hmoment

/-- **`J*^{sm}_{u,D} ≺ 1` at an arbitrary admissible pair `(Kmod, γ)`** —
`RBM.stochDom_jSfarSm_of_entriesEv` with the exponents carried. -/
theorem stochDom_jSfarSm_of_entriesEvK {Kmod γ : ℝ} (hK : 0 ≤ Kmod) (hγ : 0 < γ)
    (hst : ∀ N, s N ≤ t N) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    (hmod : EntryModulusEvK X E s t D Kmod γ)
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
  MomentDuhamelCut.stochDom_of_cutHypEv
    (cutHypEv_jSfarSm_of_entriesK X hK hγ hst hs0 ht1 hmod hmoment)
    (Filter.Eventually.of_forall fun _ => le_rfl) hinit

/-- **(5.48) at the smooth weight, with the modulus at an arbitrary admissible pair.**
`RBM.flowEq548W_of_sharp_entriesEv` with `(Kmod, γ)` carried through. -/
theorem flowEq548W_of_sharp_entriesEvK {Kmod γ : ℝ} (hK : 0 ≤ Kmod) (hγ : 0 < γ) (hE : |E| < 2)
    (hst : ∀ N, s N ≤ t N) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    (Hy : ∀ D : ℝ, 0 < D → Step2Near47.MomentHypCutSharp X E s t D)
    (hmod : ∀ D : ℝ, 0 < D → EntryModulusEvK X E s t D Kmod γ)
    (hmoment : ∀ D : ℝ, 0 < D → ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ ε > (0 : ℝ), ∀ p : ℕ,
      ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      ∀ ws ∈ MomentDuhamelCut.netFinset s t (meshK Kmod γ) N,
        ∫ ω, |MomentDuhamelCut.cutTrunc ((N : ℝ) ^ (2 * δ) * 1)
              (Step2FarMart.jSfarSm X E D N ws ω)| ^ (2 * p) ∂B.P
          ≤ C * ((N : ℝ) ^ (ε * p) * (1 : ℝ) ^ (2 * p)))
    (hinit : ∀ D : ℝ, 0 < D → StochDom B.P
      (fun N (_ : Unit) ω => Step2FarMart.jSfarSm X E D N (s N) ω) (fun _ _ _ => (1 : ℝ))) :
    Step45.FlowEq548W X E s t
      (fun N p => Step2FarMart.nearChi (B.W N : ℝ) (B.ell N p.1)
        (zdist (B.L N) (p.2.1 - p.2.2))) :=
  Step2FarMart.flowEq548W_of_jSfarSm X (near_of_sharp X Hy hE hst ht1)
    fun D hD => stochDom_jSfarSm_of_entriesEvK X hK hγ hst hs0 ht1 (hmod D hD) (hmoment D hD)
      (hinit D hD)

/-- **The parametric bundle really is the old one at `(1, 1/2)`.**  Compiled certificate: the
`Kmod = 1`, `γ = 1/2` instance of `RBM.cutHypEv_jSfarSm_of_entriesK` takes the hypotheses of
`RBM.cutHypEv_jSfarSm_of_entries` verbatim (same `EntryModulusEv` by
`RBM.entryModulusEvK_one_half`, same mesh by `RBM.meshK_one_half`) and returns the same
bundle. -/
theorem cutHypEv_jSfarSm_of_entriesK_one_half
    (hst : ∀ N, s N ≤ t N) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    (hmod : EntryModulusEv X E s t D)
    (hmoment : ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ ε > (0 : ℝ), ∀ p : ℕ, ∃ C > (0 : ℝ),
      ∀ᶠ N : ℕ in atTop,
      ∀ ws ∈ MomentDuhamelCut.netFinset s t (fun N => ((N : ℝ) + 1) ^ (2 : ℝ)) N,
        ∫ ω, |MomentDuhamelCut.cutTrunc ((N : ℝ) ^ (2 * δ) * 1)
              (Step2FarMart.jSfarSm X E D N ws ω)| ^ (2 * p) ∂B.P
          ≤ C * ((N : ℝ) ^ (ε * p) * (1 : ℝ) ^ (2 * p))) :
    Nonempty (MomentDuhamelCut.CutHypEv B.P
      (fun N u ω => Step2FarMart.jSfarSm X E D N u ω) s t (fun _ => 1)) :=
  ⟨cutHypEv_jSfarSm_of_entriesK X (Kmod := 1) (γ := 1 / 2) zero_le_one (by norm_num)
    hst hs0 ht1 ((entryModulusEvK_one_half X).2 hmod) (by rw [meshK_one_half]; exact hmoment)⟩

end Parametric

/-! ### 12. T258(甲/⑥): the refutation, with the exponents free

`RBM.ModulusEvAt` and `RBM.not_modulusEv_zero_start` were **already** parametric in
`(Kmod, γ)`; only the entrywise wrapper was not.  Closing that gap gives the precise answer to
"for which `(Kmod, γ)` does T249's verdict hold": **for every real `Kmod` and every `γ > 0`.**

The reason is visible in the proof of `RBM.not_modulusEv_zero_start`: it fixes `N` *first* and
only then chooses the time `v = min(t_N, (c/(N^{Kmod}+1))^{1/γ})`.  Since the jump `c` supplied
by `RBM.gap_lower` does not shrink with `v`, no value of `Kmod` can absorb it — a larger `Kmod`
only makes the refuting time smaller.  At `γ ≤ 0` the statement is not a modulus at all
(`|v-w|^0 = 1`), which is why `0 < γ` is carried everywhere. -/

section ParametricZeroStart

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E D : ℝ} {t : ℕ → ℝ}
variable (X : Sample B)

theorem modulusEvAt_of_entryModulusEvK {Kmod γ : ℝ}
    (h : EntryModulusEvK X E (fun _ => 0) t D Kmod γ) :
    ModulusEvAt X E D (fun _ => 0) t Kmod γ := by
  filter_upwards [h] with N hN ω v hv w hw
  exact Step2FarMart.abs_jSfarSm_sub_le X fun x =>
    (Step2FarMart.abs_lkFarSm_ratio_sub_le X x).trans (hN ω v hv w hw x)

/-- **T249's verdict, for every `(Kmod, γ)` with `0 < γ`.**  `RBM.not_entryModulusEv_zero_start`
is the case `(1, 1/2)`. -/
theorem not_entryModulusEvK_zero_start (hE : |E| ≤ 2) {Kmod γ : ℝ} (hγ : 0 < γ) {c : ℝ}
    (hc : 0 < c)
    (hbig : ∀ᶠ N : ℕ in atTop, ∀ v ∈ Set.Ioc (0 : ℝ) (t N), ∃ ω : Ω,
      1 + c ≤ Step2FarMart.jSfarSm X E D N v ω)
    (ht : ∀ᶠ N : ℕ in atTop, 0 < t N) :
    ¬ EntryModulusEvK X E (fun _ => 0) t D Kmod γ := fun h =>
  not_modulusEv_zero_start X hE hγ hc hbig ht (modulusEvAt_of_entryModulusEvK X h)

end ParametricZeroStart

section ParametricGap
variable {B : Band ℝ} {E D : ℝ}

/-- **The verdict of T249(甲) at an arbitrary pair `(Kmod, γ)` with `0 < γ`.**  Word for word
`RBM.not_entryModulusEv_swapSample_of_far`, which is the case `(1, 1/2)`; the constant `c` is
the same `1/(200((η_{t₀})⁻² + 1))` and does not depend on the exponents.

**This is the precise answer to "which `(Kmod, γ)`":** on a window starting at `0`, *all* of
them.  Parametrizing `RBM.EntryModulusEv` therefore does **not** rescue the field — only the
event restriction can, and §13 says how far that goes. -/
theorem not_entryModulusEvK_swapSample_of_far {t : ℕ → ℝ} {t₀ Kmod γ : ℝ} (hγ : 0 < γ)
    (b : ∀ N, ZMod (B.L N) × ZMod (B.L N)) (hE : |E| < 2) (hD : 2 ≤ D) (ht₀ : t₀ < 1)
    (ht0 : ∀ᶠ N : ℕ in atTop, 0 < t N) (htt : ∀ᶠ N : ℕ in atTop, t N ≤ t₀)
    (hsep : ∀ᶠ N : ℕ in atTop, (b N).1 ≠ (b N).2 ∧ ∀ v ∈ Set.Ioc (0 : ℝ) (t N),
        Step2FarMart.farChi (B.W N : ℝ) (B.ell N v) (zdist (B.L N) ((b N).1 - (b N).2)) = 1) :
    ¬ EntryModulusEvK (swapSample B b) E (fun _ => 0) t D Kmod γ := by
  refine not_entryModulusEvK_zero_start (swapSample B b) hE.le hγ
    (c := 1 / (200 * ((etaT E t₀)⁻¹ ^ 2 + 1))) (by positivity)
    (hbig_swapSample b hE ?_ ?_) ht0
  · filter_upwards [htt] with N h using lt_of_le_of_lt h ht₀
  · filter_upwards [hsep, htt] with N hsepN hle v hv
    exact ⟨hsepN.1, hsepN.2 v hv,
      gap_lower hE (B.W_pos N) (B.three_le_L N) hv.1 (hv.2.trans hle) ht₀ hD _⟩

end ParametricGap

/-! ### 13. T258: the event-restricted modulus, and exactly how far the event rescues it

§12 says the *unrestricted* field is false for **every** pair `(Kmod, γ)` with `0 < γ`, so the
only remaining repair is the event restriction of T249(丙).  T256 (`RBM.t249_witness_norm_gt`)
showed that §12's witness, taken at the refuting time `v`, has `‖X‖ = v^{-1/2} > N`, hence lies
*outside* `{‖X‖ ≤ N}` — the published refutation is silent about the event.  This section
closes that gap, and the answer is **not** that the event saves the field:

* push the time up to `v = N^{-2}`, the smallest time at which the witness `ω = v^{-1/2} = N`
  is still inside the event (`RBM.exists_jSfarSm_ge_swapSample'` now hands the bound on the
  witness out, which the bare existential could not);
* there the jump is still `≍ W_N` (`RBM.gap_lower_mul_W`: T249's estimate keeps a factor `W`
  that `RBM.gap_lower` discards), which **diverges**;
* a modulus with exponents `(Kmod, γ)` allows only `N^{Kmod - 2γ}` there.

So the event-restricted field is refuted exactly when `Kmod ≤ 2γ`, which contains the pair
`(1, 1/2)` that `RBM.EntryModulusEv` — and, downstream, `RBM.EntryModulusEvOn` — hard-codes.
D17's repair `Kmod ≥ D - 1`, `γ = 1/2` is outside that range, as it must be. -/

section EventRestricted

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E D : ℝ} {s t : ℕ → ℝ}
variable (X : Sample B)

/-- `RBM.ModulusEvAt` with the deterministic inequality asked only on an event — exactly the
`modulus` field of `RBM.MomentDuhamelCut.CutHypEvOn` for `J = J*^{sm}`. -/
def ModulusEvAtOn (X : Sample B) (E D : ℝ) (s t : ℕ → ℝ) (Kmod γ : ℝ)
    (Good : ℕ → Set Ω) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∀ ω ∈ Good N, ∀ v ∈ Set.Icc (s N) (t N), ∀ w ∈ Set.Icc (s N) (t N),
    |Step2FarMart.jSfarSm X E D N v ω - Step2FarMart.jSfarSm X E D N w ω|
      ≤ (N : ℝ) ^ Kmod * |v - w| ^ γ

/-- `RBM.EntryModulusEvK` with the inequality asked only on an event.  This is the shape
`RBM.EntryModulusEvOn` (`Flow/Thm221Assembly.lean`, downstream of this file) has, with its two
hard-coded exponents made parameters. -/
def EntryModulusEvKOn (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) (D Kmod γ : ℝ)
    (Good : ℕ → Set Ω) : Prop :=
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
          ≤ (N : ℝ) ^ Kmod * |v - w| ^ γ

/-- At `Good ≡ univ` the event-restricted field is the plain one. -/
theorem entryModulusEvKOn_univ_iff {Kmod γ : ℝ} :
    EntryModulusEvKOn X E s t D Kmod γ (fun _ => Set.univ)
      ↔ EntryModulusEvK X E s t D Kmod γ := by
  constructor
  · intro h; filter_upwards [h] with N hN ω; exact hN ω (Set.mem_univ ω)
  · intro h; filter_upwards [h] with N hN ω _; exact hN ω

theorem entryModulusEvKOn_of_entryModulusEvK {Kmod γ : ℝ} (Good : ℕ → Set Ω)
    (h : EntryModulusEvK X E s t D Kmod γ) : EntryModulusEvKOn X E s t D Kmod γ Good := by
  filter_upwards [h] with N hN ω _; exact hN ω

theorem modulusEvAtOn_of_entryModulusEvKOn {Kmod γ : ℝ} {Good : ℕ → Set Ω}
    (h : EntryModulusEvKOn X E s t D Kmod γ Good) :
    ModulusEvAtOn X E D s t Kmod γ Good := by
  filter_upwards [h] with N hN ω hω v hv w hw
  exact Step2FarMart.abs_jSfarSm_sub_le X fun x =>
    (Step2FarMart.abs_lkFarSm_ratio_sub_le X x).trans (hN ω hω v hv w hw x)

/-- **The event does not save a modulus with `Kmod ≤ 2γ`.**  At the time `v = N^{-2}` the
modulus allows a jump of at most `N^{Kmod - 2γ} ≤ 1`, while `hbig` exhibits, *inside the event*,
a jump of `g N > 1`.  The comparison point is `w = 0`, at the same `ω`, where `J*^{sm} = 1`
identically (`RBM.jSfarSm_zero`), so no second point of the event is needed. -/
theorem not_modulusEvAtOn_zero_start (hE : |E| ≤ 2) {Kmod γ : ℝ} (hKγ : Kmod ≤ 2 * γ)
    {Good : ℕ → Set Ω} {g : ℕ → ℝ}
    (hbig : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-(2 : ℝ)) ≤ t N ∧
      ∃ ω ∈ Good N, 1 + g N ≤ Step2FarMart.jSfarSm X E D N ((N : ℝ) ^ (-(2 : ℝ))) ω)
    (hg : ∀ᶠ N : ℕ in atTop, 1 < g N) :
    ¬ ModulusEvAtOn X E D (fun _ => 0) t Kmod γ Good := by
  intro hmod
  obtain ⟨N, hmodN, hbigN, hgN, hN1⟩ :=
    (hmod.and (hbig.and (hg.and (eventually_ge_atTop 1)))).exists
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  set v : ℝ := (N : ℝ) ^ (-(2 : ℝ)) with hvdef
  have hv0 : 0 < v := Real.rpow_pos_of_pos hN0 _
  obtain ⟨htv, ω, hωG, hωj⟩ := hbigN
  have hvmem : v ∈ Set.Icc ((fun _ : ℕ => (0 : ℝ)) N) (t N) := ⟨hv0.le, htv⟩
  have h0mem : (0 : ℝ) ∈ Set.Icc ((fun _ : ℕ => (0 : ℝ)) N) (t N) := ⟨le_rfl, hv0.le.trans htv⟩
  have hm := hmodN ω hωG v hvmem 0 h0mem
  rw [jSfarSm_zero X hE N ω] at hm
  have habs : |v - 0| = v := by rw [sub_zero, abs_of_nonneg hv0.le]
  rw [habs] at hm
  have hvg : v ^ γ = (N : ℝ) ^ (-(2 : ℝ) * γ) := by
    rw [hvdef, ← Real.rpow_mul hN0.le]
  have hrhs : (N : ℝ) ^ Kmod * v ^ γ ≤ 1 := by
    rw [hvg, ← Real.rpow_add hN0]
    calc (N : ℝ) ^ (Kmod + -(2 : ℝ) * γ) ≤ (N : ℝ) ^ (0 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hNR (by linarith)
      _ = 1 := Real.rpow_zero _
  have hlow : g N ≤ |Step2FarMart.jSfarSm X E D N v ω - 1| := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  linarith

/-- **The same verdict in the structural form**: no `RBM.MomentDuhamelCut.CutHypEvOn` whose
exponents satisfy `Kmod ≤ 2γ` survives the jump, event or no event. -/
theorem not_cutHypEvOn_of_jump (hE : |E| ≤ 2) {Good : ℕ → Set Ω} {g Θ : ℕ → ℝ}
    (hbig : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-(2 : ℝ)) ≤ t N ∧
      ∃ ω ∈ Good N, 1 + g N ≤ Step2FarMart.jSfarSm X E D N ((N : ℝ) ^ (-(2 : ℝ))) ω)
    (hg : ∀ᶠ N : ℕ in atTop, 1 < g N)
    (H : MomentDuhamelCut.CutHypEvOn B.P
      (fun N u ω => Step2FarMart.jSfarSm X E D N u ω) (fun _ => 0) t Θ Good)
    (hKγ : H.Kmod ≤ 2 * H.γ) : False :=
  not_modulusEvAtOn_zero_start X hE hKγ hbig hg H.modulus

end EventRestricted

section EventGap
variable {B : Band ℝ} {E D : ℝ}

/-- **The jump at the time `v = N^{-2}`, with a witness inside `{|ω| ≤ N}`.**  This is the
statement T256 could not extract from `RBM.exists_jSfarSm_ge_swapSample`: the witness bound
comes from `RBM.exists_jSfarSm_ge_swapSample'`, and the size of the jump from
`RBM.gap_lower_mul_W` (which keeps the factor `W` that `RBM.gap_lower` throws away). -/
theorem hbigOn_swapSample {t : ℕ → ℝ} {t₀ : ℝ}
    (b : ∀ N, ZMod (B.L N) × ZMod (B.L N)) (hE : |E| < 2) (hD : 2 ≤ D) (ht₀ : t₀ < 1)
    (htt : ∀ᶠ N : ℕ in atTop, t N ≤ t₀)
    (hsmall : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-(2 : ℝ)) ≤ t N)
    (hsep : ∀ᶠ N : ℕ in atTop, (b N).1 ≠ (b N).2 ∧ ∀ v ∈ Set.Ioc (0 : ℝ) (t N),
        Step2FarMart.farChi (B.W N : ℝ) (B.ell N v) (zdist (B.L N) ((b N).1 - (b N).2)) = 1) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-(2 : ℝ)) ≤ t N ∧
      ∃ ω ∈ {ω : ℝ | |ω| ≤ (N : ℝ)},
        1 + (B.W N : ℝ) / (200 * ((etaT E t₀)⁻¹ ^ 2 + 1))
          ≤ Step2FarMart.jSfarSm (swapSample B b) E D N ((N : ℝ) ^ (-(2 : ℝ))) ω := by
  filter_upwards [htt, hsmall, hsep, eventually_ge_atTop 1] with N hle hsm hsepN hN1
  refine ⟨hsm, ?_⟩
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  set v : ℝ := (N : ℝ) ^ (-(2 : ℝ)) with hvdef
  have hv0 : 0 < v := Real.rpow_pos_of_pos hN0 _
  have hvt : v ≤ t₀ := le_trans hsm hle
  have hv1 : v < 1 := lt_of_le_of_lt hvt ht₀
  have hW0 : (0 : ℝ) < (B.W N : ℝ) := by exact_mod_cast B.W_pos N
  obtain ⟨hz0, hz, hz'⟩ := zt_ne_zero_and_sq (E := E) (v := v) hE hv1
  have hfar := hsepN.2 v ⟨hv0, hsm⟩
  obtain ⟨ω, hωb, hω⟩ := exists_jSfarSm_ge_swapSample' (E := E) (D := D) b N hv0 hsepN.1
    hz0 hz hz' hfar
    (T₀ := tailT (B.W N : ℝ) (B.ell N v) (etaT E v) D
      (zdist (B.L N) ((b N).1 - (b N).2))) (tailT_pos hW0 _) le_rfl
  have hsqrt : 1 / Real.sqrt v = (N : ℝ) := by
    rw [hvdef, Real.sqrt_eq_rpow, ← Real.rpow_mul hN0.le,
      show (-(2 : ℝ)) * ((1 : ℝ) / 2) = -(1 : ℝ) by norm_num,
      Real.rpow_neg hN0.le, Real.rpow_one, one_div, inv_inv]
  have hcle : (B.W N : ℝ) / (200 * ((etaT E t₀)⁻¹ ^ 2 + 1))
      ≤ ‖((B.W N : ℂ))⁻¹ * ((1 - (zt E v) ^ 2)⁻¹ * (1 - ((starRingEnd ℂ) (zt E v)) ^ 2)⁻¹)‖
        / (2 * tailT (B.W N : ℝ) (B.ell N v) (etaT E v) D
            (zdist (B.L N) ((b N).1 - (b N).2))) :=
    gap_lower_mul_W hE (B.W_pos N) (B.three_le_L N) hv0 hvt ht₀ hD _
  exact ⟨ω, by simpa [hsqrt] using hωb, le_trans (by linarith) hω⟩

/-- **The verdict on the event.**  On a window `[0, t_N]` with `t_N ≤ t₀ < 1`, the
event-restricted entrywise modulus with exponents `(Kmod, γ)` is **false on `{|ω| ≤ N}`**
whenever `Kmod ≤ 2γ`, provided the bandwidth diverges (`hW`, which is (2.2) and more).

The pair `(1, 1/2)` that `RBM.EntryModulusEv` and `RBM.EntryModulusEvOn` hard-code satisfies
`Kmod ≤ 2γ` with equality, so the event restriction of T249(丙) does **not** by itself make the
field producible: the exponent has to grow too. -/
theorem not_entryModulusEvKOn_swapSample_of_far {t : ℕ → ℝ} {t₀ Kmod γ : ℝ}
    (b : ∀ N, ZMod (B.L N) × ZMod (B.L N)) (hE : |E| < 2) (hD : 2 ≤ D) (ht₀ : t₀ < 1)
    (hKγ : Kmod ≤ 2 * γ)
    (htt : ∀ᶠ N : ℕ in atTop, t N ≤ t₀)
    (hsmall : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-(2 : ℝ)) ≤ t N)
    (hsep : ∀ᶠ N : ℕ in atTop, (b N).1 ≠ (b N).2 ∧ ∀ v ∈ Set.Ioc (0 : ℝ) (t N),
        Step2FarMart.farChi (B.W N : ℝ) (B.ell N v) (zdist (B.L N) ((b N).1 - (b N).2)) = 1)
    (hW : ∀ᶠ N : ℕ in atTop, 200 * ((etaT E t₀)⁻¹ ^ 2 + 1) < (B.W N : ℝ)) :
    ¬ EntryModulusEvKOn (swapSample B b) E (fun _ => 0) t D Kmod γ
        (fun N => {ω : ℝ | |ω| ≤ (N : ℝ)}) := fun h =>
  not_modulusEvAtOn_zero_start (swapSample B b) hE.le hKγ
    (g := fun N => (B.W N : ℝ) / (200 * ((etaT E t₀)⁻¹ ^ 2 + 1)))
    (hbigOn_swapSample b hE hD ht₀ htt hsmall hsep)
    (by
      filter_upwards [hW] with N hN
      rw [lt_div_iff₀ (by positivity)]
      linarith)
    (modulusEvAtOn_of_entryModulusEvKOn (swapSample B b) h)

end EventGap

/-! ### 14. T258(乙): T249's verdict on a real model

T252 proved the geometric premise `hsep` for `RBM.Gauss.Dims.exampleGrow`
(`RBM.hsep_exampleGrow`, `RBM.hsep_exampleGrow_quarter`) but could not wire it in, because the
refutations of §10 live on a `RBM.Band ℝ` (the coordinate `ω` of `RBM.swapSample` is a single
real, as one Gaussian entry is) while `RBM.Gauss.band d` is carried by `RBM.Gauss.Ω d`.
`RBM.bandR` is the same `(W, L, c)` data on `ℝ`, with the standard Gaussian as its law — so
`hsep` transfers by `rfl`, every field of `RBM.Band` other than `P` coming from the same
`RBM.Gauss.Dims`.

The conclusions below are **unconditional**: no `hgap`, no `hsep`, no free constant. -/

section RealModel

open ProbabilityTheory

/-- The `RBM.Band ℝ` carried by a `RBM.Gauss.Dims`: same `W`, `L`, `c`, and (2.2), with the
standard Gaussian as the law of the single coordinate `ω`. -/
noncomputable def bandR (d : Gauss.Dims) : Band ℝ where
  P := gaussianReal 0 1
  isProbabilityMeasure := inferInstance
  W := d.W
  L := d.L
  W_pos := d.W_pos
  three_le_L := d.three_le_L
  dim := d.dim
  c := d.c
  c_pos := d.c_pos
  bandwidth := d.bandwidth

@[simp] theorem bandR_W (d : Gauss.Dims) : (bandR d).W = d.W := rfl
@[simp] theorem bandR_L (d : Gauss.Dims) : (bandR d).L = d.L := rfl

/-- The growing model of `RBM1D/Gauss/DimsExample.lean`, on `ℝ`. -/
noncomputable abbrev bandGrow : Band ℝ := bandR Gauss.Dims.exampleGrow

/-- `hsep` for `RBM.bandGrow` at the window `t_N ≡ 1/4`, `t₀ = 1/2` — T252's
`RBM.hsep_exampleGrow_quarter`, transferred by `rfl`. -/
theorem hsep_bandGrow :
    ∀ᶠ N : ℕ in atTop,
      (bHalf bandGrow N).1 ≠ (bHalf bandGrow N).2 ∧
      ∀ v ∈ Set.Ioc (0 : ℝ) ((fun _ : ℕ => (1 : ℝ) / 4) N),
        Step2FarMart.farChi ((bandGrow.W N : ℕ) : ℝ) (bandGrow.ell N v)
          (zdist (bandGrow.L N) ((bHalf bandGrow N).1 - (bHalf bandGrow N).2)) = 1 :=
  hsep_exampleGrow_quarter

/-- **T249's verdict on a real model, with the exponents free.**  For the flow
`H_u = √u · ω · A_N` on `RBM.bandGrow`, at `E = 0`, on the window `[0, 1/4]`: for **every**
`Kmod : ℝ` and **every** `γ > 0`, the entrywise modulus of (5.48) is false.  No hypothesis is
left except `2 ≤ D`. -/
theorem not_entryModulusEvK_bandGrow {D Kmod γ : ℝ} (hγ : 0 < γ) (hD : 2 ≤ D) :
    ¬ EntryModulusEvK (swapSample bandGrow (bHalf bandGrow)) 0 (fun _ => 0)
        (fun _ => 1 / 4) D Kmod γ :=
  not_entryModulusEvK_swapSample_of_far (t₀ := 1 / 2) hγ _ (by norm_num) hD (by norm_num)
    (Filter.Eventually.of_forall fun _ => by norm_num)
    (Filter.Eventually.of_forall fun _ => by norm_num) hsep_bandGrow

/-- **The hard-coded field, refuted on a real model.**  The `(Kmod, γ) = (1, 1/2)` case of
`RBM.not_entryModulusEvK_bandGrow`: `RBM.EntryModulusEv` itself has no producer here. -/
theorem not_entryModulusEv_bandGrow {D : ℝ} (hD : 2 ≤ D) :
    ¬ EntryModulusEv (swapSample bandGrow (bHalf bandGrow)) 0 (fun _ => 0)
        (fun _ => 1 / 4) D :=
  not_entryModulusEv_swapSample_of_far (t₀ := 1 / 2) _ (by norm_num) hD (by norm_num)
    (Filter.Eventually.of_forall fun _ => by norm_num)
    (Filter.Eventually.of_forall fun _ => by norm_num) hsep_bandGrow

/-- **No `RBM.MomentDuhamelCut.CutHypEv` for `J*^{sm}` on a real model**, at any threshold. -/
theorem not_cutHypEv_bandGrow {D : ℝ} (hD : 2 ≤ D) (Θ : ℕ → ℝ) :
    ¬ Nonempty (MomentDuhamelCut.CutHypEv bandGrow.P
      (fun N u ω => Step2FarMart.jSfarSm (swapSample bandGrow (bHalf bandGrow)) 0 D N u ω)
      (fun _ => 0) (fun _ => 1 / 4) Θ) :=
  not_cutHypEv_swapSample_of_far (t₀ := 1 / 2) _ (by norm_num) hD (by norm_num)
    (Filter.Eventually.of_forall fun _ => by norm_num)
    (Filter.Eventually.of_forall fun _ => by norm_num) hsep_bandGrow

/-- The bandwidth of `RBM.bandGrow` diverges, which is what §13 needs. -/
theorem eventually_lt_bandGrow_W (C : ℝ) : ∀ᶠ N : ℕ in atTop, C < (bandGrow.W N : ℝ) := by
  filter_upwards [Gauss.Dims.tendsto_growW.eventually_ge_atTop (⌈C⌉₊ + 1)] with N hN
  have h1 : ((⌈C⌉₊ : ℝ) + 1) ≤ (bandGrow.W N : ℝ) := by exact_mod_cast hN
  have h2 : C ≤ (⌈C⌉₊ : ℝ) := Nat.le_ceil C
  linarith

/-- **The event does not save it either, on the same real model.**  With `Good N = {|ω| ≤ N}`
— the event T256 identified as the one T249's published witness escapes — the entrywise
modulus is still false for every pair with `Kmod ≤ 2γ`, in particular for the hard-coded
`(1, 1/2)`.  This is the end-to-end statement T256 was one step short of. -/
theorem not_entryModulusEvKOn_bandGrow {D Kmod γ : ℝ} (hKγ : Kmod ≤ 2 * γ) (hD : 2 ≤ D) :
    ¬ EntryModulusEvKOn (swapSample bandGrow (bHalf bandGrow)) 0 (fun _ => 0)
        (fun _ => 1 / 4) D Kmod γ (fun N => {ω : ℝ | |ω| ≤ (N : ℝ)}) :=
  not_entryModulusEvKOn_swapSample_of_far (t₀ := 1 / 2) _ (by norm_num) hD (by norm_num) hKγ
    (Filter.Eventually.of_forall fun _ => by norm_num)
    (by
      filter_upwards [eventually_ge_atTop 2] with N hN
      have hNR : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
      have hrw : (N : ℝ) ^ (-(2 : ℝ)) = ((N : ℝ) ^ (2 : ℕ))⁻¹ := by
        rw [Real.rpow_neg hN0.le, ← Real.rpow_natCast (N : ℝ) 2]
        norm_num
      have h4 : (4 : ℝ) ≤ (N : ℝ) ^ (2 : ℕ) := by nlinarith
      show (N : ℝ) ^ (-(2 : ℝ)) ≤ 1 / 4
      rw [hrw, show (1 : ℝ) / 4 = (4 : ℝ)⁻¹ by norm_num]
      gcongr)
    hsep_bandGrow (eventually_lt_bandGrow_W _)

/-- **The hard-coded pair, on the event, on a real model** — the `(1, 1/2)` case. -/
theorem not_entryModulusEvKOn_one_half_bandGrow {D : ℝ} (hD : 2 ≤ D) :
    ¬ EntryModulusEvKOn (swapSample bandGrow (bHalf bandGrow)) 0 (fun _ => 0)
        (fun _ => 1 / 4) D 1 (1 / 2) (fun N => {ω : ℝ | |ω| ≤ (N : ℝ)}) :=
  not_entryModulusEvKOn_bandGrow (by norm_num) hD

end RealModel

/-! ### 15. T258: satisfiability of the parametrization

Three things have to be checked, all compiled.

1. The parametric field is **not weaker than nothing**: `γ` is carried with `0 < γ` everywhere,
   and at `γ = 0` the right-hand side would be `N^{Kmod}`, an absolute bound.
   `RBM.sat_entryModulusEvK_of_window_point` is the degenerate witness (it needs `0 < γ` to
   make the right-hand side vanish), i.e. the field is still satisfiable exactly where it says
   nothing — the same sharpness §3 recorded for the unparametrized one.
2. The **pair of net fields** that pull in opposite directions is still discharged at one and
   the same mesh, for every admissible pair (`RBM.sat_meshK_pair`), so the parametrization
   cannot make the bundle unsatisfiable through `mesh_fine`/`card_le`.
3. The exponent range left open by §13 is **non-empty**: D17's pair `Kmod = D - 1 = 59`,
   `γ = 1/2` is outside `Kmod ≤ 2γ`, so nothing here refutes it, and its mesh is the explicit
   `(N+1)^{118}` (`RBM.sat_meshK_D17`, `RBM.d17_pair_outside_event_refutation`). -/

section SatParametric

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E D : ℝ} {s t : ℕ → ℝ}
variable (X : Sample B)

/-- The degenerate witness, at an arbitrary admissible pair.  `0 < γ` is exactly what makes the
right-hand side `N^{Kmod} · 0^γ` vanish; at `γ = 0` the statement below would be an absolute
bound instead. -/
theorem sat_entryModulusEvK_of_window_point {Kmod γ : ℝ} (hγ : 0 < γ) (ht : ∀ N, t N = s N) :
    EntryModulusEvK X E s t D Kmod γ := by
  refine Filter.Eventually.of_forall fun N ω v hv w hw x => ?_
  have hv' : v = s N := le_antisymm (by rw [← ht N]; exact hv.2) hv.1
  have hw' : w = s N := le_antisymm (by rw [← ht N]; exact hw.2) hw.1
  subst hv'
  subst hw'
  simp [Real.zero_rpow hγ.ne']

/-- **The net pair is jointly satisfiable at every admissible pair**, by theorems rather than by
a witness: one mesh discharges both `mesh_fine` and `card_le`. -/
theorem sat_meshK_pair {Kmod γ : ℝ} (hK : 0 ≤ Kmod) (hγ : 0 < γ)
    (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1) :
    (∀ N : ℕ, 0 < meshK Kmod γ N) ∧
    (∀ N : ℕ, (N : ℝ) ^ Kmod * (1 / meshK Kmod γ N) ^ γ ≤ 1) ∧
    (∀ᶠ N : ℕ in atTop, (t N - s N) * meshK Kmod γ N + 2 ≤ (N : ℝ) ^ (Kmod / γ + 1)) :=
  ⟨meshK_pos Kmod γ, mesh_fine_at_meshK hK hγ, card_le_at_meshK hK hγ hs0 ht1⟩

/-- The mesh at D17's pair `Kmod = D - 1 = 59`, `γ = 1/2`, explicitly. -/
theorem sat_meshK_D17 : meshK 59 (1 / 2) = fun N : ℕ => ((N : ℝ) + 1) ^ (118 : ℝ) := by
  funext N
  norm_num [meshK]

/-- **The range left open is non-empty.**  §13 refutes the event-restricted field exactly for
`Kmod ≤ 2γ`; D17's pair `(59, 1/2)` is outside it, so this file does not refute the repair it
proposes.  (Whether that pair is *producible* is T230's question, not this one.) -/
theorem d17_pair_outside_event_refutation : ¬ ((59 : ℝ) ≤ 2 * (1 / 2 : ℝ)) := by norm_num

end SatParametric


end RBM


/-!
## Deviations (T258a)

**Paper location**: §5.3, (5.46) and (5.48); (5.27) for `T_{u,D}`.

1. **The modulus of (5.46) carries its exponents.**  `RBM.EntryModulusEvK` and
   `RBM.EntryModulusEvKOn` replace the right-hand side `(N : ℝ)^1 * |v - w|^{1/2}`, which
   `RBM.EntryModulusEv` writes into the `def`, by `(N : ℝ)^{Kmod} * |v - w|^γ` with the pair
   carried alongside `D`.  The paper never fixes these exponents: the continuity it uses in
   (5.46) is "polynomially bounded in `N`", and the `D`-dependence of `T_{u,D}` makes the
   honest exponent grow with `D` (§13; and T252's `RBM.norm_lk_sub_le_lip` gives `γ = 1`, not
   `1/2`).  So the *formalization* deviated from the paper, and this file removes the
   deviation rather than adding one.
   *Change the paper?* **No.**  *Lines*: 0 in the paper.  *Renumbering*: no.
2. **`γ` is always carried with `0 < γ`, and `Kmod` with `0 ≤ Kmod` wherever the bundle is
   produced** (`RBM.cutHypEv_jSfarSm_of_entriesK`).  At `γ = 0` the field is an absolute bound,
   not a modulus, and would be satisfied by anything bounded; at `Kmod < 0` the mesh
   `RBM.meshK` would not be `≥ 1`.  Neither restriction has a counterpart in the paper because
   the paper does not name the exponents at all.
   *Change the paper?* No.  *Lines*: 0.  *Renumbering*: no.
3. **The window of §5.3 cannot start at `0`** — already recorded by T252 (`T252a`, item 1) and
   by T249.  §12 sharpens it: the refutation holds for *every* `(Kmod, γ)` with `0 < γ`, and
   §13 shows that restricting to `{|ω| ≤ N}` only moves the boundary to `Kmod > 2γ`.  So the
   sentence §5.3 needs is `s_N ≥ N^{-C}` (T252a), not a larger `Kmod`.
   *Change the paper?* Yes, as already proposed in `T252a` item 1; nothing new here.
   *Lines*: 0 beyond `T252a`.  *Renumbering*: no.
-/
