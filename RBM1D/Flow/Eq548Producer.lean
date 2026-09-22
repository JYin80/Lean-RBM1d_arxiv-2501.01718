/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.Step2FarMart
import RBM1D.Hierarchy.Step2Near47
import RBM1D.Defs.MatrixMeasurable

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

end RBM
