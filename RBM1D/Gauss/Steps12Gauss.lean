/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Flow.Hypotheses
import RBM1D.Gauss.Step2Gauss

/-!
# Steps 1–2 of `RBM.Steps` for the Gaussian model — T1521

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*.

Packages `RBM.Steps`'s first four fields (`apriori`, `weakLaw`, `localLaw`, `aprioriDecay` —
Steps 1–2 of §2.7) as a standalone structure `RBM.Steps12`, and produces an instance of it for
the Gaussian model `sample d` from `RBM.Gauss.step2_gauss_of_grid` (T1517, Steps 2's conclusion
under `GridPointwise`) together with `RBM.Step1.apriori`/`RBM.Step1.weakLaw` (Step 1), whose
hypotheses are discharged *entirely from `step2_gauss_of_grid`'s own hypothesis list*, exactly
along the route `RBM.Step2.step2`'s own proof uses (`Hierarchy/Step2.lean:2062–2071`) to produce
its own `h1 : Step1.Hyp` and `hreg'`/`hcond` — this ticket's interface check confirms that route
needs nothing more.

## Main results

* `RBM.Steps12` — (T1): the first four fields of `RBM.Steps`, verbatim.
* `RBM.Steps.toSteps12`, `RBM.Steps.ofSteps12` — (T1): the two one-line conversions.
* `RBM.Gauss.steps12_gauss_of_grid` — (T2): `Steps12 (sample d) E s t` from `step2_gauss_of_grid`'s
  hypothesis list (`hgp : GridPointwise d E s t` included), with Step 1 discharged internally.
* `RBM.Gauss.gridPointwise_of_step2Hyp` and two `example`s — (T3): `Steps12` is not vacuous
  (it follows from `Steps`), and `steps12_gauss_of_grid`'s hypothesis list is implied by (a
  superset of) `RBM.Step2.step2`'s own hypothesis list for `sample d`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix

namespace RBM

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- **`RBM.Steps12`** — Steps 1–2 of §2.7 (the first four fields of `RBM.Steps`), stated verbatim
with the same types, as a standalone structure. -/
structure Steps12 (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) : Prop where
  /-- **(2.73)** (Step 1): `|L_{u,σ,a}| ≺ (ℓ_u/ℓ_s)^{n-1} (W ℓ_u η_u)^{-n+1}`. -/
  apriori : ∀ n : ℕ, 1 ≤ n → StochDom B.P
    (fun N (p : TimeIcc s t N × LoopData (B.L N) n) ω => ‖X.Lval E N p.1 ω p.2.idx‖)
    (fun N p _ => (B.ell N p.1 / B.ell N (s N)) ^ (n - 1) * (B.scale E N p.1)⁻¹ ^ (n - 1))
  /-- **(2.74)** (Step 1): `‖G_u - m‖_max ≺ (W ℓ_u η_u)^{-1/4}`. -/
  weakLaw : StochDom B.P
    (fun N (p : TimeIcc s t N × (B.Idx N × B.Idx N)) ω => X.llErr E N p.1 ω p.2)
    (fun N p _ => (B.scale E N p.1)⁻¹ ^ ((1 : ℝ) / 4))
  /-- **(2.75)** (Step 2): `‖G_u - m‖_max ≺ (W ℓ_u η_u)^{-1/2}`. -/
  localLaw : StochDom B.P
    (fun N (p : TimeIcc s t N × (B.Idx N × B.Idx N)) ω => X.llErr E N p.1 ω p.2)
    (fun N p _ => (B.scale E N p.1)⁻¹ ^ ((1 : ℝ) / 2))
  /-- **(2.76)** (Step 2): for `σ = (+,-)`, `|L_u - K_u| ≺ (η_s/η_u)^4 (W ℓ_u η_u)^{-2}
  (exp(-(|a₁-a₂|/ℓ_u)^{1/2}) + W^{-D})`. -/
  aprioriDecay : ∀ D : ℝ, 0 < D → StochDom B.P
    (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
      X.lkErr E N p.1 ω (pmLoop p.2.1 p.2.2))
    (fun N p _ => (etaT E (s N) / etaT E p.1) ^ 4 * (B.scale E N p.1)⁻¹ ^ 2 *
      B.decayProf N p.1 D p.2.1 p.2.2)

variable {X : Sample B} {E : ℝ} {s t : ℕ → ℝ}

/-- **`Steps` restricts to `Steps12`** (projecting its first four fields). -/
theorem Steps.toSteps12 (h : Steps X E s t) : Steps12 X E s t :=
  ⟨h.apriori, h.weakLaw, h.localLaw, h.aprioriDecay⟩

/-- **`Steps12` extends to `Steps`** given the four remaining fields (Steps 3–6). -/
theorem Steps.ofSteps12 (h : Steps12 X E s t)
    (sharpLoop : ∀ n : ℕ, 1 ≤ n → StochDom B.P
      (fun N (p : TimeIcc s t N × LoopData (B.L N) n) ω => ‖X.Lval E N p.1 ω p.2.idx‖)
      (fun N p _ => (B.scale E N p.1)⁻¹ ^ (n - 1)))
    (sharpLmK : ∀ n : ℕ, 1 ≤ n → StochDom B.P
      (fun N (p : TimeIcc s t N × LoopData (B.L N) n) ω => X.lkErr E N p.1 ω p.2.idx)
      (fun N p _ => (B.scale E N p.1)⁻¹ ^ n))
    (sharpDecay : ∀ D : ℝ, 0 < D → StochDom B.P
      (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
        X.lkErr E N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => (B.scale E N p.1)⁻¹ ^ 2 * B.decayProf N p.1 D p.2.1 p.2.2))
    (sharpExpect : UnifDetDom
      (fun N (p : TimeIcc s t N × LoopData (B.L N) 2) => X.expErr E N p.1 p.2.idx)
      (fun N _ => (B.scale E N (t N))⁻¹ ^ 3)) :
    Steps X E s t :=
  ⟨h.apriori, h.weakLaw, h.localLaw, h.aprioriDecay, sharpLoop, sharpLmK, sharpDecay, sharpExpect⟩

end RBM

namespace RBM.Gauss

variable (d : Dims)

/-- **(T2)** `Steps12 (sample d) E s t` from `step2_gauss_of_grid`'s hypothesis list (T1517),
verbatim. `localLaw`/`aprioriDecay` are `step2_gauss_of_grid`'s two conjuncts; `apriori`/`weakLaw`
come from `RBM.Step1.apriori`/`RBM.Step1.weakLaw`, whose hypotheses `hc : Cond272 (band d) E s t`,
`hreg' : ∀ᶠ N, N^c ≤ scale(t)` and `h1 : Step1.Hyp (sample d) E s t` are all discharged from this
same hypothesis list, exactly as in `Step2.step2`'s own proof (`Hierarchy/Step2.lean:2062–2071`).
This is the interface check the ticket asks for: it closes with nothing beyond the list below. -/
theorem steps12_gauss_of_grid {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) {E : ℝ} (hEκ : |E| ≤ 2 - κ)
    {s t : ℕ → ℝ} (hB : BoundsCore (sample d) E s)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c)
    (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 ≤
      (band d).scale E N (t N))
    (hgp : GridPointwise d E s t) :
    Steps12 (sample d) E s t := by
  have hE : |E| < 2 := by linarith
  have hcond : Cond272 (band d) E s t := Step2.cond272_of_strict hE hst ht1 hc0 hreg
  have hreg' : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale E N (t N) := by
    filter_upwards [Step2.eventually_R4_le_scale (B := band d) hE hst ht1 hc0 hreg] with N hN
    exact (hN ⟨t N, hst N, le_rfl⟩).2
  have h1 : Step1.Hyp (sample d) E s t :=
    step1Hyp_gauss_of_scale'' d hκ0 hEκ hB hs0 hst ht1 hcond hc0 hreg'
  obtain ⟨hlocal, hdecay⟩ := step2_gauss_of_grid d hκ0 hκ1 hEκ hB hs0 hst ht1 hc0 hreg hgp
  exact
    { apriori := Step1.apriori (sample d) hκ0 hEκ hB hs0 hst ht1 hcond hc0 hreg' h1
      weakLaw := Step1.weakLaw (sample d) hκ0 hEκ hB hs0 hst ht1 hcond hc0 hreg' h1
      localLaw := hlocal
      aprioriDecay := hdecay }

/-! ### (T3): nondegeneracy -/

/-- **(T3, helper)** `GridPointwise` (hence, composed with `steps12_gauss_of_grid`, all of its
hypotheses) is implied by `Step2.step2`'s own random-layer input `Hy` for `sample d`: `Hy` gives
(2.76) via `RBM.Step2.aprioriDecay`, which transfers to the grid at the trivial one-step grid
`K := 1`, exactly as `Step2Gauss.lean`'s own (unnamed) nonvacuity example for `GridPointwise`
does. -/
theorem gridPointwise_of_step2Hyp {κ : ℝ} (hκ0 : 0 < κ) {E : ℝ} (hEκ : |E| ≤ 2 - κ)
    {s t : ℕ → ℝ} (Hy : Step2.Hyp (sample d) E s t) (hB : BoundsCore (sample d) E s)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c)
    (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 ≤
      (band d).scale E N (t N)) :
    GridPointwise d E s t := by
  have hE : |E| < 2 := by linarith
  have h276 := Step2.aprioriDecay (sample d) Hy hE hs0 hst ht1 hB hc0 hreg
  intro D hD u
  refine ⟨fun _ => 1, fun _ => one_ne_zero, 1, zero_le_one, ?_, ?_⟩
  · filter_upwards [eventually_ge_atTop 2] with N hN
    have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    rw [show ((1 + 1 : ℕ) : ℝ) = 2 by norm_num, Real.rpow_one]
    exact hN2
  · have hpoint := (h276 D hD).precomp_param
      (fun N (p : ZMod (d.L N) × ZMod (d.L N)) => (u N, p))
    exact (stochDom_grid_iff_flow d E s (fun N => (u N : ℝ)) (fun _ => 1) hs0
      (fun N => (u N).2.1) (fun _ => one_ne_zero)
      (fun N p => (etaT E (s N) / etaT E (u N : ℝ)) ^ 4 *
        ((band d).scale E N (u N : ℝ))⁻¹ ^ 2 *
        (band d).decayProf N (u N : ℝ) D p.1 p.2)).2 hpoint

/-- **(T3, part 1)-probe**: `Steps12` is not vacuous — it follows from `Steps` (`Steps.toSteps12`),
so it is strictly weaker, not an independent (possibly-empty) assumption. -/
example {X : Sample (band d)} {E : ℝ} {s t : ℕ → ℝ} (h : Steps X E s t) : Steps12 X E s t :=
  h.toSteps12

/-- **(T3, part 2)-probe**: `steps12_gauss_of_grid`'s hypothesis list is jointly satisfiable in
the sense that it is implied by (a superset of) `Step2.step2`'s own hypothesis list for
`sample d` — `Hy : Step2.Hyp (sample d) E s t` (`Step2.step2`'s random-layer input) supplies
`hgp` via `gridPointwise_of_step2Hyp`, and everything else is shared verbatim. -/
example {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) {E : ℝ} (hEκ : |E| ≤ 2 - κ) {s t : ℕ → ℝ}
    (Hy : Step2.Hyp (sample d) E s t) (_h1 : Step1.Hyp (sample d) E s t)
    (hB : BoundsCore (sample d) E s) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c)
    (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 ≤
      (band d).scale E N (t N)) :
    Steps12 (sample d) E s t :=
  steps12_gauss_of_grid d hκ0 hκ1 hEκ hB hs0 hst ht1 hc0 hreg
    (gridPointwise_of_step2Hyp d hκ0 hEκ Hy hB hs0 hst ht1 hc0 hreg)

end RBM.Gauss
