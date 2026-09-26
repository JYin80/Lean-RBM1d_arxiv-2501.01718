/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.GridNetLift
import RBM1D.Gauss.GridJStar
import RBM1D.Gauss.EntryBoundTime
import RBM1D.Hierarchy.Step2

/-!
# `Step2.step2`'s conclusion for the Gaussian model, without `Hy` — T1517

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*.

`RBM.Step2.step2`'s conclusion — (2.75) and (2.76) — packaged for the Gaussian model `sample d`,
with the random-layer hypothesis `RBM.Step2.Hyp` (`Hy`) removed: its only use in `step2`'s own
proof is to produce (2.76) via `aprioriDecay`, and (2.76) is exactly what T1511's
`RBM.Gauss.Grid.h276_of_pointwise` produces from a pointwise (single-time) input `hpt` instead.
`Step1.Hyp` (`h1`) is likewise removed and discharged internally by
`RBM.Gauss.step1Hyp_gauss_of_scale''`.

## Main results

* `RBM.Gauss.step2_gauss_of_pointwise` — (T1): `step2`'s conclusion for `sample d`, from `hpt`.
* `RBM.Gauss.lkErrMat`, `RBM.Gauss.GridPointwise` — (T2, data): the matrix-level `lkErr` and the
  grid-side hypothesis that R4c is to discharge.
* `RBM.Gauss.stochDom_grid_iff_flow` — (T2, the transfer): the grid `StochDom` at the last grid
  step *equals* the flow `StochDom` at the matching time (`Grid.map_H_eq` + `Grid.time_last`; no
  loss, since `StochDom` only involves the laws at each fixed `N`).
* `RBM.Gauss.hpt_of_grid` — (T2): `hpt` from `GridPointwise`.
* `RBM.Gauss.step2_gauss_of_grid` — (T3): (T1) composed with (T2), under `GridPointwise`.
-/

noncomputable section

namespace RBM.Gauss

open MeasureTheory ProbabilityTheory Filter Matrix RBM

variable (d : Dims)

/-! ### (T2, data): the matrix-level `lkErr` -/

/-- **`lkErrMat`** — the matrix-level `Sample.lkErr`: `‖gloop M (zt E u) I − Kval E N u I‖`,
taking the matrix `M` directly instead of a `Sample`'s `ω`. Exactly `RBM.Gauss.Grid.jSMat`'s
pattern (`Gauss/GridJStar.lean`), for `lkErr` instead of `jS`. -/
def lkErrMat (E : ℝ) (N : ℕ) (u : ℝ) (M : Matrix (d.Idx N) (d.Idx N) ℂ)
    (I : LoopIdx (ZMod (d.L N))) : ℝ :=
  ‖gloop (d.L N) (d.W N) M (zt E u) I - (band d).Kval E N u I‖

/-- **Measurability of `lkErrMat` in the matrix `M`**, unconditionally, from
`Grid.measurable_gloop_matrix`. -/
theorem measurable_lkErrMat (E : ℝ) (N : ℕ) (u : ℝ) (I : LoopIdx (ZMod (d.L N))) :
    Measurable fun M : Matrix (d.Idx N) (d.Idx N) ℂ => lkErrMat d E N u M I :=
  ((Grid.measurable_gloop_matrix d N (zt E u) I).sub measurable_const).norm

/-- **`sample d`'s `lkErr` is `lkErrMat` evaluated at `Hflow d N u ω`.** Literally `rfl`: `band
d`'s `L`/`W`/`P` are `d`'s by structure projection, and `sample d`'s `H` is `Hflow d` by
definition, exactly the reason `Grid.jS_eq_jSMat` is `rfl`. -/
theorem lkErr_eq_lkErrMat (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω d) (I : LoopIdx (ZMod (d.L N))) :
    (sample d).lkErr E N u ω I = lkErrMat d E N u (Hflow d N u ω) I := rfl

/-! ### (T2, the transfer) -/

/-- **The grid transfer.** For a fixed grid `K` (`K N ≠ 0` for every `N`) reaching `u N` from
`s N`, the grid `StochDom` of the last grid step's `lkErrMat` equals the flow `StochDom` of
`(sample d).lkErr` at `u N`. The two failure-event probabilities are *equal* at every `N`
(`Grid.map_H_eq` at `k = K N`, `time … (K N) = u N` by `Grid.time_last`), so the transfer costs
nothing: it holds for *every* grid resolution `K`, not just a specific one. -/
theorem stochDom_grid_iff_flow (E : ℝ) (s uR : ℕ → ℝ) (K : ℕ → ℕ)
    (hs0 : ∀ N, 0 ≤ s N) (hsu : ∀ N, s N ≤ uR N) (hK0 : ∀ N, K N ≠ 0)
    (ζ : ∀ N, ZMod (d.L N) × ZMod (d.L N) → ℝ) :
    StochDom (Grid.Pg d)
        (fun N (p : ZMod (d.L N) × ZMod (d.L N)) ω =>
          lkErrMat d E N (uR N) (Grid.H d s uR K N (K N) ω) (pmLoop p.1 p.2))
        (fun N p _ => ζ N p)
      ↔ StochDom (P d)
        (fun N (p : ZMod (d.L N) × ZMod (d.L N)) ω =>
          (sample d).lkErr E N (uR N) ω (pmLoop p.1 p.2))
        (fun N p _ => ζ N p) := by
  have hSmeas : ∀ (N : ℕ) (τ : ℝ), MeasurableSet
      {M : Matrix (d.Idx N) (d.Idx N) ℂ |
        ∃ p : ZMod (d.L N) × ZMod (d.L N),
          (N : ℝ) ^ τ * ζ N p < lkErrMat d E N (uR N) M (pmLoop p.1 p.2)} := by
    intro N τ
    have heq : {M : Matrix (d.Idx N) (d.Idx N) ℂ |
        ∃ p : ZMod (d.L N) × ZMod (d.L N),
          (N : ℝ) ^ τ * ζ N p < lkErrMat d E N (uR N) M (pmLoop p.1 p.2)}
        = ⋃ p : ZMod (d.L N) × ZMod (d.L N),
          {M | (N : ℝ) ^ τ * ζ N p < lkErrMat d E N (uR N) M (pmLoop p.1 p.2)} := by
      ext M; simp
    rw [heq]
    exact MeasurableSet.iUnion fun p =>
      measurableSet_lt measurable_const (measurable_lkErrMat d E N (uR N) (pmLoop p.1 p.2))
  have hmapeq : ∀ N : ℕ,
      (Grid.Pg d).map (Grid.H d s uR K N (K N)) = (P d).map (Hflow d N (uR N)) := by
    intro N
    have h := Grid.map_H_eq (d := d) s uR K N (K N) (hs0 N) (hsu N) (hK0 N)
    rwa [Grid.time_last s uR K N (hK0 N)] at h
  have hHmeas : ∀ N : ℕ, Measurable (Grid.H d s uR K N (K N)) := fun N =>
    (Grid.H_measurable_filt d s uR K N (K N)).mono ((Grid.filt d).le (K N)) le_rfl
  have hHflowmeas : ∀ N : ℕ, Measurable (Hflow d N (uR N)) := fun N =>
    RBM.measurable_H (sample d) N (uR N)
  have hmeasEq : ∀ (N : ℕ) (τ : ℝ),
      (Grid.Pg d) (RBM.badSet
          (fun N (p : ZMod (d.L N) × ZMod (d.L N)) ω =>
            lkErrMat d E N (uR N) (Grid.H d s uR K N (K N) ω) (pmLoop p.1 p.2))
          (fun N p _ => ζ N p) τ N)
        = (P d) (RBM.badSet
          (fun N (p : ZMod (d.L N) × ZMod (d.L N)) ω =>
            (sample d).lkErr E N (uR N) ω (pmLoop p.1 p.2))
          (fun N p _ => ζ N p) τ N) := by
    intro N τ
    have hL : RBM.badSet
        (fun N (p : ZMod (d.L N) × ZMod (d.L N)) ω =>
          lkErrMat d E N (uR N) (Grid.H d s uR K N (K N) ω) (pmLoop p.1 p.2))
        (fun N p _ => ζ N p) τ N
        = (Grid.H d s uR K N (K N)) ⁻¹'
          {M | ∃ p : ZMod (d.L N) × ZMod (d.L N),
            (N : ℝ) ^ τ * ζ N p < lkErrMat d E N (uR N) M (pmLoop p.1 p.2)} := by
      ext ω; simp [RBM.badSet]
    have hR : RBM.badSet
        (fun N (p : ZMod (d.L N) × ZMod (d.L N)) ω =>
          (sample d).lkErr E N (uR N) ω (pmLoop p.1 p.2))
        (fun N p _ => ζ N p) τ N
        = (Hflow d N (uR N)) ⁻¹'
          {M | ∃ p : ZMod (d.L N) × ZMod (d.L N),
            (N : ℝ) ^ τ * ζ N p < lkErrMat d E N (uR N) M (pmLoop p.1 p.2)} := by
      ext ω
      simp only [RBM.badSet, Set.mem_setOf_eq, Set.mem_preimage]
      refine exists_congr fun p => ?_
      rw [show (sample d).lkErr E N (uR N) ω (pmLoop p.1 p.2)
          = lkErrMat d E N (uR N) (Hflow d N (uR N) ω) (pmLoop p.1 p.2) from
        lkErr_eq_lkErrMat d E N (uR N) ω (pmLoop p.1 p.2)]
    rw [hL, hR, ← Measure.map_apply (hHmeas N) (hSmeas N τ),
      ← Measure.map_apply (hHflowmeas N) (hSmeas N τ), hmapeq N]
  constructor
  · intro h τ hτ D hD
    filter_upwards [h τ hτ D hD] with N hN
    rw [← hmeasEq N τ]; exact hN
  · intro h τ hτ D hD
    filter_upwards [h τ hτ D hD] with N hN
    rw [hmeasEq N τ]; exact hN

/-- **`GridPointwise`** — the grid-side hypothesis that R4c is to discharge: for every endpoint
sequence `u N ∈ [s N, t N]`, every `D > 0`, there is a grid of `K N + 1 ≤ N^C` points from `s N`
to `u N` along which the last grid step's `lkErrMat` obeys the (2.76) bound. By
`stochDom_grid_iff_flow`, this is (for whatever `K` a proof of it produces) exactly the pointwise
flow statement `hpt` of `Grid.h276_of_pointwise`. -/
def GridPointwise (E : ℝ) (s t : ℕ → ℝ) : Prop :=
  ∀ D : ℝ, 0 < D → ∀ u : ∀ N, TimeIcc s t N,
    ∃ K : ℕ → ℕ, (∀ N, K N ≠ 0) ∧ ∃ C : ℝ, 0 ≤ C ∧
      (∀ᶠ N : ℕ in atTop, ((K N + 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ C) ∧
      StochDom (Grid.Pg d)
        (fun N (p : ZMod (d.L N) × ZMod (d.L N)) ω =>
          lkErrMat d E N (u N : ℝ) (Grid.H d s (fun N => (u N : ℝ)) K N (K N) ω)
            (pmLoop p.1 p.2))
        (fun N p _ => (etaT E (s N) / etaT E (u N : ℝ)) ^ 4 *
          ((band d).scale E N (u N : ℝ))⁻¹ ^ 2 *
          (band d).decayProf N (u N : ℝ) D p.1 p.2)

/-- **(T2)** `hpt` (`Grid.h276_of_pointwise`'s pointwise input) from `GridPointwise`. -/
theorem hpt_of_grid {E : ℝ} {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N)
    (hG : GridPointwise d E s t) :
    ∀ D : ℝ, 0 < D → ∀ u : ∀ N, TimeIcc s t N, StochDom (P d)
      (fun N (p : ZMod (d.L N) × ZMod (d.L N)) ω =>
        (sample d).lkErr E N (u N) ω (pmLoop p.1 p.2))
      (fun N p _ => (etaT E (s N) / etaT E (u N)) ^ 4 *
        ((band d).scale E N (u N))⁻¹ ^ 2 * (band d).decayProf N (u N) D p.1 p.2) := by
  intro D hD u
  obtain ⟨K, hK0, C, hC0, hKcard, hgrid⟩ := hG D hD u
  exact (stochDom_grid_iff_flow d E s (fun N => (u N : ℝ)) K hs0 (fun N => (u N).2.1) hK0
    (fun N p => (etaT E (s N) / etaT E (u N : ℝ)) ^ 4 *
      ((band d).scale E N (u N : ℝ))⁻¹ ^ 2 * (band d).decayProf N (u N : ℝ) D p.1 p.2)).1 hgrid

/-! ### (T1) -/

/-- **(T1)** `Step2.step2`'s conclusion for the Gaussian model `sample d`, from a pointwise
(single-time, along every sequence `u`) input `hpt`, exactly `Grid.h276_of_pointwise`'s. `Hy`
and `Step1.Hyp` are both gone: `Step1.Hyp` is discharged internally by
`step1Hyp_gauss_of_scale''`, and `hpt` (via `Grid.h276_of_pointwise`) replaces `aprioriDecay`.
The route is `step2`'s own proof (`Hierarchy/Step2.lean:2066–2071`) verbatim, with `h276`'s
source swapped. -/
theorem step2_gauss_of_pointwise {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) {E : ℝ}
    (hEκ : |E| ≤ 2 - κ) {s t : ℕ → ℝ} (hB : BoundsCore (sample d) E s)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c)
    (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 ≤
      (band d).scale E N (t N))
    (hpt : ∀ D : ℝ, 0 < D → ∀ u : ∀ N, TimeIcc s t N, StochDom (P d)
      (fun N (p : ZMod (d.L N) × ZMod (d.L N)) ω =>
        (sample d).lkErr E N (u N) ω (pmLoop p.1 p.2))
      (fun N p _ => (etaT E (s N) / etaT E (u N)) ^ 4 *
        ((band d).scale E N (u N))⁻¹ ^ 2 * (band d).decayProf N (u N) D p.1 p.2)) :
    StochDom (band d).P
      (fun N (p : TimeIcc s t N × ((band d).Idx N × (band d).Idx N)) ω =>
        (sample d).llErr E N p.1 ω p.2)
      (fun N p _ => ((band d).scale E N p.1)⁻¹ ^ ((1 : ℝ) / 2)) ∧
    ∀ D : ℝ, 0 < D → StochDom (band d).P
      (fun N (p : TimeIcc s t N × (ZMod ((band d).L N) × ZMod ((band d).L N))) ω =>
        (sample d).lkErr E N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => (etaT E (s N) / etaT E p.1) ^ 4 * ((band d).scale E N p.1)⁻¹ ^ 2 *
        (band d).decayProf N p.1 D p.2.1 p.2.2) := by
  have hE : |E| < 2 := by linarith
  have h276 := Grid.h276_of_pointwise d hE hs0 hst ht1 hc0 hreg hpt
  have hc272 : Cond272 (band d) E s t := Step2.cond272_of_strict hE hst ht1 hc0 hreg
  have hreg' : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale E N (t N) := by
    filter_upwards [Step2.eventually_R4_le_scale (B := band d) hE hst ht1 hc0 hreg] with N hN
    exact (hN ⟨t N, hst N, le_rfl⟩).2
  have h1 : Step1.Hyp (sample d) E s t :=
    step1Hyp_gauss_of_scale'' d hκ0 hEκ hB hs0 hst ht1 hc272 hc0 hreg'
  have h274 := Step1.weakLaw (sample d) hκ0 hEκ hB hs0 hst ht1 hc272 hc0 hreg' h1
  exact ⟨Step2.localLaw (sample d) hκ0 hκ1 hEκ hs0 hst ht1 hc0 hreg h276 h274 h1.lemma41, h276⟩

/-- **(T1)-probe**: `step2_gauss_of_pointwise`'s conclusion, as an explicit type, is syntactically
`Step2.step2`'s conclusion at `X := sample d`, `B := band d`. -/
example {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) {E : ℝ} (hEκ : |E| ≤ 2 - κ) {s t : ℕ → ℝ}
    (hB : BoundsCore (sample d) E s) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c)
    (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 ≤
      (band d).scale E N (t N))
    (hpt : ∀ D : ℝ, 0 < D → ∀ u : ∀ N, TimeIcc s t N, StochDom (P d)
      (fun N (p : ZMod (d.L N) × ZMod (d.L N)) ω =>
        (sample d).lkErr E N (u N) ω (pmLoop p.1 p.2))
      (fun N p _ => (etaT E (s N) / etaT E (u N)) ^ 4 *
        ((band d).scale E N (u N))⁻¹ ^ 2 * (band d).decayProf N (u N) D p.1 p.2)) :
    StochDom (band d).P
      (fun N (p : TimeIcc s t N × ((band d).Idx N × (band d).Idx N)) ω =>
        (sample d).llErr E N p.1 ω p.2)
      (fun N p _ => ((band d).scale E N p.1)⁻¹ ^ ((1 : ℝ) / 2)) ∧
    ∀ D : ℝ, 0 < D → StochDom (band d).P
      (fun N (p : TimeIcc s t N × (ZMod ((band d).L N) × ZMod ((band d).L N))) ω =>
        (sample d).lkErr E N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => (etaT E (s N) / etaT E p.1) ^ 4 * ((band d).scale E N p.1)⁻¹ ^ 2 *
        (band d).decayProf N p.1 D p.2.1 p.2.2) :=
  step2_gauss_of_pointwise d hκ0 hκ1 hEκ hB hs0 hst ht1 hc0 hreg hpt

/-! ### (T3) -/

/-- **(T3)** `Step2.step2`'s conclusion for `sample d`, under the grid-side `GridPointwise`
(the composite of (T1) and (T2)). This is what R4c's `GridPointwise …` closes G1b with. -/
theorem step2_gauss_of_grid {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) {E : ℝ} (hEκ : |E| ≤ 2 - κ)
    {s t : ℕ → ℝ} (hB : BoundsCore (sample d) E s)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c)
    (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 ≤
      (band d).scale E N (t N))
    (hgp : GridPointwise d E s t) :
    StochDom (band d).P
      (fun N (p : TimeIcc s t N × ((band d).Idx N × (band d).Idx N)) ω =>
        (sample d).llErr E N p.1 ω p.2)
      (fun N p _ => ((band d).scale E N p.1)⁻¹ ^ ((1 : ℝ) / 2)) ∧
    ∀ D : ℝ, 0 < D → StochDom (band d).P
      (fun N (p : TimeIcc s t N × (ZMod ((band d).L N) × ZMod ((band d).L N))) ω =>
        (sample d).lkErr E N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => (etaT E (s N) / etaT E p.1) ^ 4 * ((band d).scale E N p.1)⁻¹ ^ 2 *
        (band d).decayProf N p.1 D p.2.1 p.2.2) :=
  step2_gauss_of_pointwise d hκ0 hκ1 hEκ hB hs0 hst ht1 hc0 hreg (hpt_of_grid d hs0 hgp)

/-- **`GridPointwise` is not vacuous**: it is implied by `step2`'s own conclusion for `sample d`
(the second conjunct), via `precomp_param` (restricting the joint statement to a fixed time
sequence `u`) and `stochDom_grid_iff_flow` (the flow-to-grid direction of the transfer, at the
trivial one-step grid `K := 1`). -/
example {E : ℝ} {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N)
    (hconcl : ∀ D : ℝ, 0 < D → StochDom (P d)
      (fun N (p : TimeIcc s t N × (ZMod (d.L N) × ZMod (d.L N))) ω =>
        (sample d).lkErr E N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => (etaT E (s N) / etaT E p.1) ^ 4 * ((band d).scale E N p.1)⁻¹ ^ 2 *
        (band d).decayProf N p.1 D p.2.1 p.2.2)) :
    GridPointwise d E s t := by
  intro D hD u
  refine ⟨fun _ => 1, fun _ => one_ne_zero, 1, zero_le_one, ?_, ?_⟩
  · filter_upwards [eventually_ge_atTop 2] with N hN
    have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    rw [show ((1 + 1 : ℕ) : ℝ) = 2 by norm_num, Real.rpow_one]
    exact hN2
  · have hpoint := (hconcl D hD).precomp_param
      (fun N (p : ZMod (d.L N) × ZMod (d.L N)) => (u N, p))
    exact (stochDom_grid_iff_flow d E s (fun N => (u N : ℝ)) (fun _ => 1) hs0
      (fun N => (u N).2.1) (fun _ => one_ne_zero)
      (fun N p => (etaT E (s N) / etaT E (u N : ℝ)) ^ 4 *
        ((band d).scale E N (u N : ℝ))⁻¹ ^ 2 *
        (band d).decayProf N (u N : ℝ) D p.1 p.2)).2 hpoint

end RBM.Gauss
