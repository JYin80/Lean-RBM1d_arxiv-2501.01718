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
theorem exists_jSfarSm_ge_swapSample
    (b : ∀ N, ZMod (B.L N) × ZMod (B.L N)) (N : ℕ) {v : ℝ} (hv : 0 < v)
    (hne : (b N).1 ≠ (b N).2) (hz0 : zt E v ≠ 0)
    (hz : 1 - (zt E v) ^ 2 ≠ 0) (hz' : 1 - ((starRingEnd ℂ) (zt E v)) ^ 2 ≠ 0)
    (hfar : Step2FarMart.farChi (B.W N : ℝ) (B.ell N v) (zdist (B.L N) ((b N).1 - (b N).2)) = 1)
    {T₀ : ℝ} (_hT₀ : 0 < T₀)
    (hT : tailT (B.W N : ℝ) (B.ell N v) (etaT E v) D
        (zdist (B.L N) ((b N).1 - (b N).2)) ≤ T₀) :
    ∃ ω : ℝ, 1 + ‖((B.W N : ℂ))⁻¹ *
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
  have hpick : ∃ ω : ℝ, ‖Lv‖ / 2 ≤ ‖Step2.lk (swapSample B b) E N v ω aa‖ := by
    rcases le_total ‖Step2.lk (swapSample B b) E N v (1 / Real.sqrt v) aa‖
      ‖Step2.lk (swapSample B b) E N v 0 aa‖ with h | h
    · exact ⟨0, by linarith⟩
    · exact ⟨1 / Real.sqrt v, by linarith⟩
  obtain ⟨ω, hω⟩ := hpick
  refine ⟨ω, ?_⟩
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
theorem gap_lower {E v D : ℝ} (hE : |E| < 2) {W L : ℕ} (hW : 1 ≤ W) (hL : 3 ≤ L)
    (hv0 : 0 < v) {t₀ : ℝ} (hvt : v ≤ t₀) (ht₀ : t₀ < 1) (hD : 2 ≤ D) (d : ℝ) :
    1 / (200 * ((etaT E t₀)⁻¹ ^ 2 + 1))
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
  calc 1 / (200 * ((etaT E t₀)⁻¹ ^ 2 + 1))
      ≤ (1 / (100 * (W : ℝ))) / (2 * (((W : ℝ) ^ 2)⁻¹ * ((etaT E t₀)⁻¹ ^ 2 + 1))) := by
        have hkey : (1 / (100 * (W : ℝ))) / (2 * (((W : ℝ) ^ 2)⁻¹ * ((etaT E t₀)⁻¹ ^ 2 + 1)))
            = (W : ℝ) / (200 * ((etaT E t₀)⁻¹ ^ 2 + 1)) := by
          field_simp
          ring
        rw [hkey]
        gcongr
    _ ≤ ‖((W : ℂ))⁻¹ * ((1 - (zt E v) ^ 2)⁻¹ * (1 - ((starRingEnd ℂ) (zt E v)) ^ 2)⁻¹)‖
          / (2 * tailT (W : ℝ) (ellHat L (v : ℂ)) (etaT E v) D d) := by
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


end RBM
