/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.FastDecayFlow
import RBM1D.Gauss.Lemma514QRoute

/-!
# T237: the measurable core of the good events, and the event-restricted kernel estimates

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.5 and §7, (7.13)/(7.16).

## The gap this file closes

T201's five kernel estimates (`RBM.Gauss.momNorm_Uker_Qop_le` and siblings) carry their
fast-decay premise `hGd` **quantified over every sample point**.  That shape is what the
project's satisfiability discipline forbids: at `ω` with `H = 0` the resolvent is the constant
`-z⁻¹`, `L - K` does not decay at the flow's radius, and no small `δ` exists.  T220's
`RBM.FastDecayFlow.momNorm_Uker_Qop_event_le` and its three siblings are the event-restricted
replacements, but they conclude a bound on the **truncated** tensor `1_Ξ A`, and getting back
to `A` is `RBM.Gauss.momNorm_le_affine_on_event`, which asks for `MeasurableSet Ξ` — while the
good event `RBM.FastDecayFlow.lkGood` is an intersection over the *uncountable*
`RBM.TimeIcc`, so its measurability is not free.

The resolution is T222's: **no measurability is needed**.  Replace `Ξ` by its *measurable
core*

`RBM.Gauss.measCore P Ξ = (toMeasurable P Ξᶜ)ᶜ`,

a measurable **subset** of `Ξ` whose complement has the *same* (outer) measure.  Being a
subset, it inherits every event-restricted hypothesis; having the same complement measure, it
inherits `RBM.HighProb` verbatim.  The continuity-in-time route (intersect over a countable
dense subset) is not needed.

## Contents

* §1 `RBM.Gauss.measCore` and its four properties, plus the transport of `RBM.HighProb` and of
  non-emptiness.  This is the only new mathematics here.
* §2 the cores of the model's two good events, `RBM.Gauss.lkGoodM` and
  `RBM.Gauss.gLoopDecayM`, with `RBM.HighProb`, measurability, and (7.13) on them.
* §3 `RBM.Gauss.momNorm_le_indicator_add_env` — Minkowski's tail, i.e. the passage from the
  truncated variable to the untruncated one, and its measurability-free form
  `RBM.Gauss.momNorm_le_indicator_measCore_add_env`.
* §4 the four kernel estimates of T201 with the decay premise **event-restricted** and the
  conclusion about the **untruncated** tensor.  These are the consumers the ticket asks for:
  no `∀ ω` decay hypothesis occurs in them.
* §5 the `Qop` half of the `hEnv…` slots, from `RBM.SumZeroDyn.norm_Qop_le_of_fastDecay`.
* §6 satisfiability: the core is non-empty with high probability, quoting T220's
  `RBM.FastDecayFlow.highProb_lkGood` and `RBM.FastDecayFlow.nonempty_of_highProb`.

The anti-vacuity guard is `RBM.Gauss.nonempty_of_measureReal_compl_lt_one`: §4's Markov
premise `(P Ξᶜ).toReal ≤ pr` with `pr < 1` already *forces* `Ξ` to be non-empty, so the
event-restricted shape cannot be satisfied by truncating everything to `0`.

## Deviation from the paper

`T237a` (temporary number): the event on which (7.13) is read is the measurable core of the
paper's good event rather than the good event itself.  The two have the same probability
(`RBM.Gauss.measure_compl_measCore`), so no estimate changes; the core is used only because
Lean's `MeasureTheory.integral_add_compl` needs a measurable set.

Nothing here is an `axiom` and nothing here is `sorry`.
-/

namespace RBM.Gauss

open MeasureTheory Filter MomentDuhamel
open RBM.SumZeroDyn

/-! ### §1  The measurable core of an event -/

section Core

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The measurable core of `Ξ`**: the complement of a measurable hull of `Ξᶜ`.

It is a measurable subset of `Ξ` whose complement has the same outer measure as `Ξᶜ`.  Every
hypothesis of the form `∀ ω ∈ Ξ, …` therefore holds on it, and `RBM.HighProb` transports to
it unchanged. -/
noncomputable def measCore (P : Measure Ω) (Ξ : Set Ω) : Set Ω := (toMeasurable P Ξᶜ)ᶜ

theorem measurableSet_measCore (P : Measure Ω) (Ξ : Set Ω) :
    MeasurableSet (measCore P Ξ) :=
  (measurableSet_toMeasurable P Ξᶜ).compl

theorem measCore_subset (P : Measure Ω) (Ξ : Set Ω) : measCore P Ξ ⊆ Ξ := by
  intro ω hω
  by_contra h
  exact hω (subset_toMeasurable P Ξᶜ h)

/-- **The core costs nothing**: its complement has the same measure as `Ξᶜ`. -/
theorem measure_compl_measCore (P : Measure Ω) (Ξ : Set Ω) :
    P (measCore P Ξ)ᶜ = P Ξᶜ := by
  rw [measCore, compl_compl]
  exact measure_toMeasurable Ξᶜ

theorem measureReal_compl_measCore (P : Measure Ω) (Ξ : Set Ω) :
    (P (measCore P Ξ)ᶜ).toReal = (P Ξᶜ).toReal := by
  rw [measure_compl_measCore]

/-- **`RBM.HighProb` transports to the core.** -/
theorem highProb_measCore {P : Measure Ω} {Ξ : ℕ → Set Ω} (h : HighProb P Ξ) :
    HighProb P (fun N => measCore P (Ξ N)) := by
  intro D hD
  filter_upwards [h D hD] with N hN
  rw [measure_compl_measCore]
  exact hN

/-- **The core is eventually non-empty** — the anti-vacuity statement for §4: truncating to a
set that could be empty would make every decay premise a statement about the zero tensor.
Quotes T220's `RBM.FastDecayFlow.nonempty_of_highProb`. -/
theorem nonempty_measCore {P : Measure Ω} [IsProbabilityMeasure P] {Ξ : ℕ → Set Ω}
    (h : HighProb P Ξ) : ∀ᶠ N : ℕ in atTop, (measCore P (Ξ N)).Nonempty :=
  FastDecayFlow.nonempty_of_highProb (highProb_measCore h)

/-- **The event-restricted estimates of §4 cannot be made vacuous by an empty event.**  Their
Markov premise is `(P Ξᶜ).toReal ≤ pr`; as soon as `pr < 1` — and it has to be far smaller
than that for the conclusion to say anything — the event is non-empty.  So there is no way to
satisfy §4's hypotheses by truncating everything to `0`. -/
theorem nonempty_of_measureReal_compl_lt_one {P : Measure Ω} [IsProbabilityMeasure P]
    {Ξ : Set Ω} {pr : ℝ} (hpr : pr < 1) (hP : (P Ξᶜ).toReal ≤ pr) : Ξ.Nonempty := by
  rw [Set.nonempty_iff_ne_empty]
  intro hemp
  rw [hemp, Set.compl_empty, measure_univ] at hP
  simp only [ENNReal.toReal_one] at hP
  linarith

end Core

/-! ### §2  The cores of the model's two good events

`RBM.FastDecayFlow.lkGood` is an intersection over `RBM.TimeIcc s t N × RBM.LoopData …`, whose
first factor is uncountable, and `RBM.LKDecayQuant.GLoopDecayEvent` likewise; neither is
visibly measurable.  Their cores are, and they carry every consequence the flow needs. -/

section ModelEvents

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {X : Sample B} {E : ℝ} {s t : ℕ → ℝ}

/-- **The measurable core of the good event (5.75).** -/
noncomputable def lkGoodM (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) (m : ℕ) (τ τ₁ D : ℝ)
    (N : ℕ) : Set Ω :=
  measCore B.P (FastDecayFlow.lkGood X E s t m τ τ₁ D N)

theorem measurableSet_lkGoodM (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) (m : ℕ) (τ τ₁ D : ℝ)
    (N : ℕ) : MeasurableSet (lkGoodM X E s t m τ τ₁ D N) :=
  measurableSet_measCore _ _

theorem lkGoodM_subset (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) (m : ℕ) (τ τ₁ D : ℝ) (N : ℕ) :
    lkGoodM X E s t m τ τ₁ D N ⊆ FastDecayFlow.lkGood X E s t m τ τ₁ D N :=
  measCore_subset _ _

theorem measure_compl_lkGoodM (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) (m : ℕ) (τ τ₁ D : ℝ)
    (N : ℕ) : B.P (lkGoodM X E s t m τ τ₁ D N)ᶜ
      = B.P (FastDecayFlow.lkGood X E s t m τ τ₁ D N)ᶜ :=
  measure_compl_measCore _ _

/-- **(5.75) ⇒ the core holds with high probability** — T220's
`RBM.FastDecayFlow.highProb_lkGood` composed with §1. -/
theorem highProb_lkGoodM (hdec : LKDecay X E s t) {m : ℕ} (hm : 1 ≤ m) {τ τ₁ D : ℝ}
    (hτ : 0 < τ) (hτ₁ : 0 < τ₁) (hD : 0 < D) :
    HighProb B.P (lkGoodM X E s t m τ τ₁ D) :=
  highProb_measCore (FastDecayFlow.highProb_lkGood hdec hm hτ hτ₁ hD)

/-- **The core of the good event is eventually non-empty.**  This is the anti-vacuity
statement of §4: the decay premises there are read on `lkGoodM`, and a version in which that
set could be empty would be worthless.  Quotes T220 twice — `highProb_lkGood` and
`nonempty_of_highProb` — and proves nothing again. -/
theorem nonempty_lkGoodM [IsProbabilityMeasure B.P] (hdec : LKDecay X E s t) {m : ℕ}
    (hm : 1 ≤ m) {τ τ₁ D : ℝ} (hτ : 0 < τ) (hτ₁ : 0 < τ₁) (hD : 0 < D) :
    ∀ᶠ N : ℕ in atTop, (lkGoodM X E s t m τ τ₁ D N).Nonempty :=
  nonempty_measCore (FastDecayFlow.highProb_lkGood hdec hm hτ hτ₁ hD)

/-- **(7.13) for `L - K` on the core**, at the radius `ℓ_u N^τ` the kernel estimates read it
at: `RBM.FastDecayFlow.fastDecay_lkT_of_mem_lkGood` through the inclusion. -/
theorem fastDecay_lkT_of_mem_lkGoodM {m N : ℕ} {τ τ₁ D u : ℝ} (hsu : s N ≤ u) (hut : u ≤ t N)
    {ω : Ω} (hω : ω ∈ lkGoodM X E s t m τ τ₁ D N) (σ : Fin m → Bool) :
    FastDecay (B.L N) (ellHat (B.L N) ((u : ℝ) : ℂ) * (N : ℝ) ^ τ)
      ((N : ℝ) ^ τ₁ * (N : ℝ) ^ (-D)) (lkT X E N u ω σ) :=
  FastDecayFlow.fastDecay_lkT_of_mem_lkGood hsu hut (lkGoodM_subset X E s t m τ τ₁ D N hω) σ

/-- **The measurable core of Definition 5.8's `G`-loop decay event.** -/
noncomputable def gLoopDecayM (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) (m : ℕ) (τ D : ℝ)
    (N : ℕ) : Set Ω :=
  measCore B.P (LKDecayQuant.GLoopDecayEvent X E s t m τ D N)

theorem measurableSet_gLoopDecayM (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) (m : ℕ) (τ D : ℝ)
    (N : ℕ) : MeasurableSet (gLoopDecayM X E s t m τ D N) :=
  measurableSet_measCore _ _

theorem gLoopDecayM_subset (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) (m : ℕ) (τ D : ℝ) (N : ℕ) :
    gLoopDecayM X E s t m τ D N ⊆ LKDecayQuant.GLoopDecayEvent X E s t m τ D N :=
  measCore_subset _ _

theorem measure_compl_gLoopDecayM (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) (m : ℕ) (τ D : ℝ)
    (N : ℕ) : B.P (gLoopDecayM X E s t m τ D N)ᶜ
      = B.P (LKDecayQuant.GLoopDecayEvent X E s t m τ D N)ᶜ :=
  measure_compl_measCore _ _

theorem highProb_gLoopDecayM (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    (h : LKDecayQuant.FlowInputs X E s t) {m : ℕ} (hm : 1 ≤ m) {τ : ℝ} (hτ : 0 < τ) {D : ℝ}
    (hD : 0 < D) : HighProb B.P (gLoopDecayM X E s t m τ D) :=
  highProb_measCore
    (LKDecayQuant.highProb_gLoopDecay_of_flowInputs hE hs0 ht1 h hm hτ hD)

/-- **(7.13) for `E ⊗ E` on the core** of the `G`-loop decay event. -/
theorem fastDecay_eeFun_of_mem_gLoopDecayM {n N : ℕ} {τ D u : ℝ} (hsu : s N ≤ u)
    (hut : u ≤ t N) {ω : Ω} (hω : ω ∈ gLoopDecayM X E s t (2 * (n + 2) + 2) τ D N)
    (σ : Fin (n + 2) → Bool) :
    FastDecay (B.L N) (ellHat (B.L N) ((u : ℝ) : ℂ) * (N : ℝ) ^ τ)
      ((B.W N : ℝ) * ((n + 2 : ℕ) : ℝ) * ((B.L N : ℝ) * (N : ℝ) ^ (-D)))
      (MomentDuhamel.eeFun B E N u (X.H N u ω) σ) :=
  FastDecayFlow.fastDecay_eeFun_of_mem_gLoopDecay hsu hut
    (gLoopDecayM_subset X E s t (2 * (n + 2) + 2) τ D N hω) σ

end ModelEvents

/-! ### §3  From the truncated variable back to the untruncated one

T220's estimates bound `‖U ∘ T(1_Ξ A)‖` in `L^q`; what the route consumes is
`‖U ∘ T(A)‖`.  The two differ only off `Ξ`, where a deterministic envelope and Markov pay the
bill.  This is the tail half of `RBM.Gauss.momNorm_le_affine_on_event`, isolated so that the
main term can be *any* bound on the truncated moment norm rather than a pointwise affine
majorant — which is what T220's conclusions are. -/

section Untruncate

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Minkowski's tail.**  `‖Z‖_q ≤ ‖1_Ξ Z‖_q + Env · P(Ξᶜ)^{1/q}`. -/
theorem momNorm_le_indicator_add_env [IsProbabilityMeasure P] {q : ℕ} (hq : q ≠ 0)
    {Z : Ω → ℝ} (hZint : Integrable (fun ω => |Z ω| ^ q) P)
    {Ξ : Set Ω} (hΞ : MeasurableSet Ξ) {Env pr : ℝ} (hEnv : 0 ≤ Env) (hpr : 0 ≤ pr)
    (hZall : ∀ ω, |Z ω| ≤ Env) (hP : (P Ξᶜ).toReal ≤ pr) :
    momNorm P q Z ≤ momNorm P q (Set.indicator Ξ Z) + Env * pr ^ ((1 : ℝ) / q) := by
  classical
  have hq0 : (0 : ℝ) ≤ (1 : ℝ) / q := by positivity
  have hq1 : (1 : ℝ) / q ≤ 1 := by
    rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hq)]
    exact_mod_cast Nat.one_le_iff_ne_zero.2 hq
  set Z' : Ω → ℝ := Set.indicator Ξ Z with hZ'def
  have hind : (fun ω => |Z' ω| ^ q) = Set.indicator Ξ (fun ω => |Z ω| ^ q) := by
    funext ω
    by_cases hω : ω ∈ Ξ
    · rw [Set.indicator_of_mem hω, hZ'def, Set.indicator_of_mem hω]
    · rw [Set.indicator_of_notMem hω, hZ'def, Set.indicator_of_notMem hω, abs_zero,
        zero_pow hq]
  have hZ'int : ∫ ω, |Z' ω| ^ q ∂P = ∫ ω in Ξ, |Z ω| ^ q ∂P := by
    rw [hind, integral_indicator hΞ]
  have hcompl : ∫ ω in Ξᶜ, |Z ω| ^ q ∂P ≤ Env ^ q * pr := by
    have hmono : ∫ ω in Ξᶜ, |Z ω| ^ q ∂P ≤ ∫ _ω in Ξᶜ, Env ^ q ∂P :=
      setIntegral_mono_on hZint.integrableOn integrableOn_const
        hΞ.compl (fun ω _ => pow_le_pow_left₀ (abs_nonneg _) (hZall ω) q)
    refine hmono.trans ?_
    rw [setIntegral_const, smul_eq_mul, measureReal_def, mul_comm]
    exact mul_le_mul_of_nonneg_left hP (by positivity)
  have hsplit : ∫ ω, |Z ω| ^ q ∂P
      = (∫ ω in Ξ, |Z ω| ^ q ∂P) + ∫ ω in Ξᶜ, |Z ω| ^ q ∂P :=
    (integral_add_compl hΞ hZint).symm
  have hZ'0 : (0 : ℝ) ≤ ∫ ω, |Z' ω| ^ q ∂P :=
    integral_nonneg fun _ => pow_nonneg (abs_nonneg _) _
  have hpow : (momNorm P q Z') ^ q = ∫ ω, |Z' ω| ^ q ∂P := by
    rw [momNorm, one_div]
    exact Real.rpow_inv_natCast_pow hZ'0 hq
  have hbound : ∫ ω, |Z ω| ^ q ∂P ≤ (momNorm P q Z') ^ q + Env ^ q * pr := by
    rw [hsplit, hpow, ← hZ'int]
    exact add_le_add le_rfl hcompl
  have hstep := Real.rpow_le_rpow (integral_nonneg fun _ => pow_nonneg (abs_nonneg _) _)
    hbound hq0
  rw [← momNorm] at hstep
  refine hstep.trans ?_
  have hsub : ((momNorm P q Z') ^ q + Env ^ q * pr) ^ ((1 : ℝ) / q)
      ≤ ((momNorm P q Z') ^ q) ^ ((1 : ℝ) / q) + (Env ^ q * pr) ^ ((1 : ℝ) / q) :=
    Real.rpow_add_le_add_rpow (pow_nonneg (momNorm_nonneg P q Z') q)
      (mul_nonneg (pow_nonneg hEnv q) hpr) hq0 hq1
  refine hsub.trans (le_of_eq ?_)
  have h1 : ((momNorm P q Z') ^ q) ^ ((1 : ℝ) / q) = momNorm P q Z' := by
    rw [one_div]; exact Real.pow_rpow_inv_natCast (momNorm_nonneg P q Z') hq
  have h2 : (Env ^ q * pr) ^ ((1 : ℝ) / q) = Env * pr ^ ((1 : ℝ) / q) := by
    rw [Real.mul_rpow (by positivity) hpr, one_div,
      Real.pow_rpow_inv_natCast hEnv hq]
  rw [h1, h2]

/-- **The same with no measurability hypothesis on `Ξ`** — the point of the ticket.  The
truncation is performed on the measurable core of §1, which is a subset of `Ξ` (so every
`∀ ω ∈ Ξ, …` premise survives) with the same complement measure (so the Markov price is
unchanged). -/
theorem momNorm_le_indicator_measCore_add_env [IsProbabilityMeasure P] {q : ℕ} (hq : q ≠ 0)
    {Z : Ω → ℝ} (hZint : Integrable (fun ω => |Z ω| ^ q) P)
    (Ξ : Set Ω) {Env pr : ℝ} (hEnv : 0 ≤ Env) (hpr : 0 ≤ pr)
    (hZall : ∀ ω, |Z ω| ≤ Env) (hP : (P Ξᶜ).toReal ≤ pr) :
    momNorm P q Z
      ≤ momNorm P q (Set.indicator (measCore P Ξ) Z) + Env * pr ^ ((1 : ℝ) / q) :=
  momNorm_le_indicator_add_env hq hZint (measurableSet_measCore P Ξ) hEnv hpr hZall
    (by rw [measureReal_compl_measCore]; exact hP)

variable {L : ℕ}

omit [MeasurableSpace Ω] in
/-- **The truncation passes through any operator that kills `0`.**  Used to recognise T220's
left-hand side `‖U ∘ T(1_Ξ A) a‖` as `1_Ξ ‖U ∘ T(A) a‖`, so that §3's tail applies.  This is
`RBM.FastDecayFlow.Uker_indicator` for a general composite. -/
theorem norm_apply_indicator_eq {m m' : ℕ} {T : (LoopArg L m → ℂ) → LoopArg L m' → ℂ}
    (hT0 : T 0 = 0) {Ξ : Set Ω} (A : Ω → LoopArg L m → ℂ) (a : LoopArg L m') (ω : Ω) :
    ‖T (Set.indicator Ξ A ω) a‖
      = Set.indicator Ξ (fun ω => ‖T (A ω) a‖) ω := by
  classical
  by_cases hω : ω ∈ Ξ
  · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω]
  · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω, hT0]
    simp


omit [MeasurableSpace Ω] in
/-- The same for the size envelope: a bound on `T(A ω)` that is uniform in the tensor slot
survives the truncation, because `T 0 = 0` and the bound is non-negative. -/
theorem norm_apply_indicator_le {m m' : ℕ} {T : (LoopArg L m → ℂ) → LoopArg L m' → ℂ}
    (hT0 : T 0 = 0) {Ξ : Set Ω} {A : Ω → LoopArg L m → ℂ} {g : Ω → ℝ}
    (hg : ∀ ω, 0 ≤ g ω) (h : ∀ ω b, ‖T (A ω) b‖ ≤ g ω) (ω : Ω) (b : LoopArg L m') :
    ‖T (Set.indicator Ξ A ω) b‖ ≤ g ω := by
  classical
  by_cases hω : ω ∈ Ξ
  · rw [Set.indicator_of_mem hω]; exact h ω b
  · rw [Set.indicator_of_notMem hω, hT0]
    simpa using hg ω

end Untruncate

/-! ### §4  T201's kernel estimates with the decay premise event-restricted

These are the consumers the ticket asks for.  Compare T201's
`RBM.Gauss.momNorm_Uker_Qop_le`: its `hGd` slot is `∀ ω, FastDecay …`, a shape the
satisfiability discipline forbids.  Here the decay is asked **only on `Ξ`**, the conclusion is
about the **untruncated** tensor, and `Ξ` carries *no* measurability hypothesis — §1 supplies
its measurable core internally.  The price is the last three premises: a deterministic
envelope `Env` for the kernel value, integrability, and a bound `pr` on `P(Ξᶜ)`;
`RBM.Gauss.eventually_env_mul_prob_rpow_le` (T218) turns `RBM.HighProb` into the statement
that `Env · pr^{1/q}` is eventually below any `N^{-D}`. -/

section EventRestricted

open RBM.MomentDuhamel

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Terms 1 and 2 of `momentDuhamelQ`, with (7.13) asked only on `Ξ`.** -/
theorem momNorm_Uker_Qop_event_untrunc_le [IsProbabilityMeasure P] (L : ℕ) [NeZero L]
    (hL : 3 ≤ L) {q : ℕ} (hq : q ≠ 0) {n : ℕ} {E : ℝ} (hE : |E| ≤ 2) (σ : Fin (n + 2) → Bool)
    {s u v : ℝ} (hs0 : 0 ≤ s) (hsu : s ≤ u) (huv : u ≤ v) (hv0 : 0 ≤ v) (hv1 : v < 1)
    {κA : ℝ} (hκA : 0 < κA) {K M ζ δ : ℝ} (hK : 1 ≤ K) (hM : 0 ≤ M) (hζ : 0 ≤ ζ) (hδ : 0 ≤ δ)
    {Ξ : Set Ω} {A : Ω → LoopArg L (n + 2) → ℂ} {ψ : Ω → ℝ} (hψ0 : ∀ ω, 0 ≤ ψ ω)
    (hint : Integrable (fun ω => ψ ω ^ q) P)
    (hGM : ∀ ω b, ‖Qop L ((u : ℝ) : ℂ) (A ω) b‖
      ≤ (κA * ((1 - u) * ellHat L (u : ℂ)))⁻¹ ^ (n + 2) * ψ ω + ζ)
    (hAM : ∀ ω ∈ Ξ, ∀ b, ‖A ω b‖ ≤ M)
    (hAd : ∀ ω ∈ Ξ, FastDecay L (ellHat L ((u : ℝ) : ℂ) * K) δ (A ω))
    (a : LoopArg L (n + 2)) {Env pr : ℝ} (hEnv : 0 ≤ Env) (hpr : 0 ≤ pr)
    (hZall : ∀ ω, ‖Uker L (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
      (Qop L ((u : ℝ) : ℂ) (A ω)) a‖ ≤ Env)
    (hZint : Integrable (fun ω => ‖Uker L (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
      (Qop L ((u : ℝ) : ℂ) (A ω)) a‖ ^ q) P)
    (hP : (P Ξᶜ).toReal ≤ pr) :
    momNorm P q (fun ω => ‖Uker L (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
        (Qop L ((u : ℝ) : ℂ) (A ω)) a‖)
      ≤ (cKerSumZero (n + 2) * K ^ (2 * (n + 2))
            * (κA * ((1 - v) * ellHat L (v : ℂ)))⁻¹ ^ (n + 2) * momNorm P q ψ
        + (cKerSumZero (n + 2) * K ^ (2 * (n + 2)) * ((1 - s) / (1 - v)) ^ (n + 2) * ζ
          + cKerSumZeroErr (n + 2) * (L : ℝ) ^ (n + 2) * ((1 - s) / (1 - v)) ^ (n + 2)
              * FastDecayFlow.qopErr1 L n K M δ))
        + Env * pr ^ ((1 : ℝ) / q) := by
  classical
  have hu0 : (0 : ℝ) ≤ u := hs0.trans hsu
  have hu1 : u < 1 := huv.trans_lt hv1
  have hℓ0 : (0 : ℝ) < ellHat L ((u : ℝ) : ℂ) := by
    have := half_le_ellHat_real L hL hu0 hu1; linarith
  have hbase : (0 : ℝ) < κA * ((1 - u) * ellHat L ((u : ℝ) : ℂ)) :=
    mul_pos hκA (mul_pos (by linarith) hℓ0)
  have hpw : (0 : ℝ) ≤ (κA * ((1 - u) * ellHat L ((u : ℝ) : ℂ)))⁻¹ ^ (n + 2) :=
    pow_nonneg (inv_nonneg.2 hbase.le) _
  have hT0 : (fun A' : LoopArg L (n + 2) → ℂ => Qop L ((u : ℝ) : ℂ) A') 0 = 0 :=
    FastDecayFlow.Qop_zero L _
  have hU0 : (fun A' : LoopArg L (n + 2) → ℂ =>
      Uker L (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ) (Qop L ((u : ℝ) : ℂ) A')) 0 = 0 := by
    change Uker L (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
      (Qop L ((u : ℝ) : ℂ) (0 : LoopArg L (n + 2) → ℂ)) = 0
    rw [FastDecayFlow.Qop_zero L]
    exact FastDecayFlow.Uker_zero (xiOf (mSigma E) σ) _ _
  -- the event-restricted estimate, on the measurable core
  have key := FastDecayFlow.momNorm_Uker_Qop_event_le (P := P) L hL hq hE σ hs0 hsu huv hv0
    hv1 hκA hK hM hζ hδ (Ξ := measCore P Ξ) (A := A) (ψ := ψ) hψ0 hint
    (norm_apply_indicator_le hT0
      (g := fun ω => (κA * ((1 - u) * ellHat L ((u : ℝ) : ℂ)))⁻¹ ^ (n + 2) * ψ ω + ζ)
      (fun ω => add_nonneg (mul_nonneg hpw (hψ0 ω)) hζ) hGM)
    (fun ω hω => hAM ω (measCore_subset P Ξ hω))
    (fun ω hω => hAd ω (measCore_subset P Ξ hω)) a
  have heq : (fun ω => ‖Uker L (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
        (Qop L ((u : ℝ) : ℂ) (Set.indicator (measCore P Ξ) A ω)) a‖)
      = Set.indicator (measCore P Ξ) (fun ω =>
          ‖Uker L (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
            (Qop L ((u : ℝ) : ℂ) (A ω)) a‖) := by
    funext ω
    exact norm_apply_indicator_eq
      (T := fun A' : LoopArg L (n + 2) → ℂ =>
        Uker L (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ) (Qop L ((u : ℝ) : ℂ) A'))
      hU0 A a ω
  rw [heq] at key
  have tail := momNorm_le_indicator_measCore_add_env (P := P) hq
    (Z := fun ω => ‖Uker L (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
      (Qop L ((u : ℝ) : ℂ) (A ω)) a‖)
    (by simpa only [abs_norm] using hZint) Ξ hEnv hpr
    (fun ω => by rw [abs_of_nonneg (norm_nonneg _)]; exact hZall ω) hP
  linarith


/-- **Term 3 of `momentDuhamelQ` (5.99), with (7.13) asked only on `Ξ`.**  As in T220, no
decay of the tensor is used at all — only the Ward bound (5.96) on its slot sums, and that
only on `Ξ`. -/
theorem momNorm_Uker_commS_event_untrunc_le [IsProbabilityMeasure P] (L : ℕ) [NeZero L]
    (hL : 3 ≤ L) {q : ℕ} (hq : q ≠ 0) {n : ℕ} {E : ℝ} (hE : |E| ≤ 2) (σ : Fin (n + 2) → Bool)
    {s u v : ℝ} (hs0 : 0 ≤ s) (hsu : s ≤ u) (huv : u ≤ v) (hv0 : 0 ≤ v) (hv1 : v < 1)
    {κA : ℝ} (hκA : 0 < κA) {K Pb ζ : ℝ} (hK : 1 ≤ K) (hζ : 0 ≤ ζ) (hP0 : 0 ≤ Pb)
    {Ξ : Set Ω} {A : Ω → LoopArg L (n + 2) → ℂ} {ψ : Ω → ℝ} (hψ0 : ∀ ω, 0 ≤ ψ ω)
    (hint : Integrable (fun ω => ψ ω ^ q) P)
    (hGM : ∀ ω b, ‖commS L (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) (A ω) b‖
      ≤ (κA * ((1 - u) * ellHat L (u : ℂ)))⁻¹ ^ (n + 2) * ψ ω + ζ)
    (hAP : ∀ ω ∈ Ξ, ∀ x, ‖Psum L (A ω) x‖ ≤ Pb)
    (a : LoopArg L (n + 2)) {Env pr : ℝ} (hEnv : 0 ≤ Env) (hpr : 0 ≤ pr)
    (hZall : ∀ ω, ‖Uker L (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
      (commS L (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) (A ω)) a‖ ≤ Env)
    (hZint : Integrable (fun ω => ‖Uker L (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
      (commS L (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) (A ω)) a‖ ^ q) P)
    (hPr : (P Ξᶜ).toReal ≤ pr) :
    momNorm P q (fun ω => ‖Uker L (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
        (commS L (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) (A ω)) a‖)
      ≤ (cKerSumZero (n + 2) * (4 * K) ^ (2 * (n + 2))
            * (κA * ((1 - v) * ellHat L (v : ℂ)))⁻¹ ^ (n + 2) * momNorm P q ψ
        + (cKerSumZero (n + 2) * (4 * K) ^ (2 * (n + 2)) * ((1 - s) / (1 - v)) ^ (n + 2) * ζ
          + cKerSumZeroErr (n + 2) * (L : ℝ) ^ (n + 2) * ((1 - s) / (1 - v)) ^ (n + 2)
              * FastDecayFlow.commErr L n (ellHat L ((u : ℝ) : ℂ)) u K Pb))
        + Env * pr ^ ((1 : ℝ) / q) := by
  classical
  have hu0 : (0 : ℝ) ≤ u := hs0.trans hsu
  have hu1 : u < 1 := huv.trans_lt hv1
  have hℓ0 : (0 : ℝ) < ellHat L ((u : ℝ) : ℂ) := by
    have := half_le_ellHat_real L hL hu0 hu1; linarith
  have hbase : (0 : ℝ) < κA * ((1 - u) * ellHat L ((u : ℝ) : ℂ)) :=
    mul_pos hκA (mul_pos (by linarith) hℓ0)
  have hpw : (0 : ℝ) ≤ (κA * ((1 - u) * ellHat L ((u : ℝ) : ℂ)))⁻¹ ^ (n + 2) :=
    pow_nonneg (inv_nonneg.2 hbase.le) _
  have hT0 : (fun A' : LoopArg L (n + 2) → ℂ =>
      commS L (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) A') 0 = 0 :=
    FastDecayFlow.commS_zero L (n := n + 1) (xiOf (mSigma E) σ) _
  have hU0 : (fun A' : LoopArg L (n + 2) → ℂ =>
      Uker L (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
        (commS L (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) A')) 0 = 0 := by
    change Uker L (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
      (commS L (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) (0 : LoopArg L (n + 2) → ℂ)) = 0
    rw [FastDecayFlow.commS_zero L (n := n + 1)]
    exact FastDecayFlow.Uker_zero (xiOf (mSigma E) σ) _ _
  have key := FastDecayFlow.momNorm_Uker_commS_event_le (P := P) L hL hq hE σ hs0 hsu huv hv0
    hv1 hκA hK hζ hP0 (Ξ := measCore P Ξ) (A := A) (ψ := ψ) hψ0 hint
    (norm_apply_indicator_le hT0
      (g := fun ω => (κA * ((1 - u) * ellHat L ((u : ℝ) : ℂ)))⁻¹ ^ (n + 2) * ψ ω + ζ)
      (fun ω => add_nonneg (mul_nonneg hpw (hψ0 ω)) hζ) hGM)
    (fun ω hω => hAP ω (measCore_subset P Ξ hω)) a
  have heq : (fun ω => ‖Uker L (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
        (commS L (xiOf (mSigma E) σ) ((u : ℝ) : ℂ)
          (Set.indicator (measCore P Ξ) A ω)) a‖)
      = Set.indicator (measCore P Ξ) (fun ω =>
          ‖Uker L (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
            (commS L (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) (A ω)) a‖) := by
    funext ω
    exact norm_apply_indicator_eq
      (T := fun A' : LoopArg L (n + 2) → ℂ =>
        Uker L (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
          (commS L (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) A'))
      hU0 A a ω
  rw [heq] at key
  have tail := momNorm_le_indicator_measCore_add_env (P := P) hq
    (Z := fun ω => ‖Uker L (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
      (commS L (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) (A ω)) a‖)
    (by simpa only [abs_norm] using hZint) Ξ hEnv hpr
    (fun ω => by rw [abs_of_nonneg (norm_nonneg _)]; exact hZall ω) hPr
  linarith

/-- **Term 4 of `momentDuhamelQ` (5.100), with (7.13) asked only on `Ξ`.** -/
theorem momNorm_Uker_dot_event_untrunc_le [IsProbabilityMeasure P] (L : ℕ) [NeZero L]
    (hL : 3 ≤ L) {q : ℕ} (hq : q ≠ 0) {n : ℕ} {E : ℝ} (hE : |E| ≤ 2) (σ : Fin (n + 2) → Bool)
    {s u v : ℝ} (hs0 : 0 ≤ s) (hsu : s ≤ u) (huv : u ≤ v) (hv0 : 0 ≤ v) (hv1 : v < 1)
    {κA : ℝ} (hκA : 0 < κA) {K Pb ζ : ℝ} (hK : 1 ≤ K) (hζ : 0 ≤ ζ) (hP0 : 0 ≤ Pb)
    {Ξ : Set Ω} {A : Ω → LoopArg L (n + 2) → ℂ} {ψ : Ω → ℝ} (hψ0 : ∀ ω, 0 ≤ ψ ω)
    (hint : Integrable (fun ω => ψ ω ^ q) P)
    (hGM : ∀ (ω : Ω) (b : LoopArg L (n + 2)),
      ‖Psum L (A ω) (b 0) * varthetaDot L (n := n + 1) u b‖
      ≤ (κA * ((1 - u) * ellHat L (u : ℂ)))⁻¹ ^ (n + 2) * ψ ω + ζ)
    (hAP : ∀ ω ∈ Ξ, ∀ x, ‖Psum L (A ω) x‖ ≤ Pb)
    (a : LoopArg L (n + 2)) {Env pr : ℝ} (hEnv : 0 ≤ Env) (hpr : 0 ≤ pr)
    (hZall : ∀ ω, ‖Uker L (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
      (fun b : LoopArg L (n + 2) =>
        Psum L (A ω) (b 0) * varthetaDot L (n := n + 1) u b) a‖ ≤ Env)
    (hZint : Integrable (fun ω => ‖Uker L (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
      (fun b : LoopArg L (n + 2) =>
        Psum L (A ω) (b 0) * varthetaDot L (n := n + 1) u b) a‖ ^ q) P)
    (hPr : (P Ξᶜ).toReal ≤ pr) :
    momNorm P q (fun ω => ‖Uker L (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
        (fun b : LoopArg L (n + 2) =>
          Psum L (A ω) (b 0) * varthetaDot L (n := n + 1) u b) a‖)
      ≤ (cKerSumZero (n + 2) * (4 * K) ^ (2 * (n + 2))
            * (κA * ((1 - v) * ellHat L (v : ℂ)))⁻¹ ^ (n + 2) * momNorm P q ψ
        + (cKerSumZero (n + 2) * (4 * K) ^ (2 * (n + 2)) * ((1 - s) / (1 - v)) ^ (n + 2) * ζ
          + cKerSumZeroErr (n + 2) * (L : ℝ) ^ (n + 2) * ((1 - s) / (1 - v)) ^ (n + 2)
              * FastDecayFlow.dotErr n (ellHat L ((u : ℝ) : ℂ)) u K Pb))
        + Env * pr ^ ((1 : ℝ) / q) := by
  classical
  have hu0 : (0 : ℝ) ≤ u := hs0.trans hsu
  have hu1 : u < 1 := huv.trans_lt hv1
  have hℓ0 : (0 : ℝ) < ellHat L ((u : ℝ) : ℂ) := by
    have := half_le_ellHat_real L hL hu0 hu1; linarith
  have hbase : (0 : ℝ) < κA * ((1 - u) * ellHat L ((u : ℝ) : ℂ)) :=
    mul_pos hκA (mul_pos (by linarith) hℓ0)
  have hpw : (0 : ℝ) ≤ (κA * ((1 - u) * ellHat L ((u : ℝ) : ℂ)))⁻¹ ^ (n + 2) :=
    pow_nonneg (inv_nonneg.2 hbase.le) _
  have hT0 : (fun A' : LoopArg L (n + 2) → ℂ => fun b : LoopArg L (n + 2) =>
      Psum L A' (b 0) * varthetaDot L (n := n + 1) u b) 0 = 0 := by
    funext b
    change Psum L (0 : LoopArg L (n + 2) → ℂ) (b 0) * varthetaDot L (n := n + 1) u b = 0
    rw [FastDecayFlow.Psum_zero L, zero_mul]
  have hU0 : (fun A' : LoopArg L (n + 2) → ℂ =>
      Uker L (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
        (fun b : LoopArg L (n + 2) =>
          Psum L A' (b 0) * varthetaDot L (n := n + 1) u b)) 0 = 0 := by
    change Uker L (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
      (fun b : LoopArg L (n + 2) =>
        Psum L (0 : LoopArg L (n + 2) → ℂ) (b 0) * varthetaDot L (n := n + 1) u b) = 0
    rw [show (fun b : LoopArg L (n + 2) =>
        Psum L (0 : LoopArg L (n + 2) → ℂ) (b 0) * varthetaDot L (n := n + 1) u b)
          = (0 : LoopArg L (n + 2) → ℂ) from hT0]
    exact FastDecayFlow.Uker_zero (xiOf (mSigma E) σ) _ _
  have key := FastDecayFlow.momNorm_Uker_dot_event_le (P := P) L hL hq hE σ hs0 hsu huv hv0
    hv1 hκA hK hζ hP0 (Ξ := measCore P Ξ) (A := A) (ψ := ψ) hψ0 hint
    (norm_apply_indicator_le
      (T := fun A' : LoopArg L (n + 2) → ℂ => fun b : LoopArg L (n + 2) =>
        Psum L A' (b 0) * varthetaDot L (n := n + 1) u b) hT0
      (g := fun ω => (κA * ((1 - u) * ellHat L ((u : ℝ) : ℂ)))⁻¹ ^ (n + 2) * ψ ω + ζ)
      (fun ω => add_nonneg (mul_nonneg hpw (hψ0 ω)) hζ) hGM)
    (fun ω hω => hAP ω (measCore_subset P Ξ hω)) a
  have heq : (fun ω => ‖Uker L (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
        (fun b : LoopArg L (n + 2) =>
          Psum L (Set.indicator (measCore P Ξ) A ω) (b 0)
            * varthetaDot L (n := n + 1) u b) a‖)
      = Set.indicator (measCore P Ξ) (fun ω =>
          ‖Uker L (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
            (fun b : LoopArg L (n + 2) =>
              Psum L (A ω) (b 0) * varthetaDot L (n := n + 1) u b) a‖) := by
    funext ω
    exact norm_apply_indicator_eq
      (T := fun A' : LoopArg L (n + 2) → ℂ =>
        Uker L (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
          (fun b : LoopArg L (n + 2) =>
            Psum L A' (b 0) * varthetaDot L (n := n + 1) u b))
      hU0 A a ω
  rw [heq] at key
  have tail := momNorm_le_indicator_measCore_add_env (P := P) hq
    (Z := fun ω => ‖Uker L (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
      (fun b : LoopArg L (n + 2) =>
        Psum L (A ω) (b 0) * varthetaDot L (n := n + 1) u b) a‖)
    (by simpa only [abs_norm] using hZint) Ξ hEnv hpr
    (fun ω => by rw [abs_of_nonneg (norm_nonneg _)]; exact hZall ω) hPr
  linarith

/-- **Term 5 of `momentDuhamelQ` (5.103), with (7.13) asked only on `Ξ`.** -/
theorem momNorm_Uker_QQ_event_untrunc_le [IsProbabilityMeasure P] (L : ℕ) [NeZero L]
    (hL : 3 ≤ L) {q : ℕ} (hq : q ≠ 0) {n : ℕ} {E : ℝ} (hE : |E| < 2) (σ : Fin (n + 2) → Bool)
    {s u v : ℝ} (hs0 : 0 ≤ s) (hsu : s ≤ u) (huv : u ≤ v) (hv0 : 0 ≤ v) (hv1 : v < 1)
    {κA : ℝ} (hκA : 0 < κA) {K e ζ δ : ℝ} (hK : 1 ≤ K) (hζ : 0 ≤ ζ) (he : 0 ≤ e) (hδ : 0 ≤ δ)
    {Ξ : Set Ω} {A : Ω → LoopArg L ((n + 2) + (n + 2)) → ℂ} {ψ : Ω → ℝ}
    (hψ0 : ∀ ω, 0 ≤ ψ ω) (hint : Integrable (fun ω => ψ ω ^ q) P)
    (hGM : ∀ ω b, ‖QQ L ((u : ℝ) : ℂ) (A ω) b‖
      ≤ (κA * ((1 - u) * ellHat L (u : ℂ)))⁻¹ ^ ((n + 2) + (n + 2)) * ψ ω + ζ)
    (hAe : ∀ ω ∈ Ξ, ∀ c, ‖A ω c‖ ≤ e)
    (hAd : ∀ ω ∈ Ξ, FastDecay L (ellHat L ((u : ℝ) : ℂ) * K) δ (A ω))
    (a : LoopArg L ((n + 2) + (n + 2))) {Env pr : ℝ} (hEnv : 0 ≤ Env) (hpr : 0 ≤ pr)
    (hZall : ∀ ω, ‖Uker L (xi2 E σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
      (QQ L ((u : ℝ) : ℂ) (A ω)) a‖ ≤ Env)
    (hZint : Integrable (fun ω => ‖Uker L (xi2 E σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
      (QQ L ((u : ℝ) : ℂ) (A ω)) a‖ ^ q) P)
    (hPr : (P Ξᶜ).toReal ≤ pr) :
    momNorm P q (fun ω => ‖Uker L (xi2 E σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
        (QQ L ((u : ℝ) : ℂ) (A ω)) a‖)
      ≤ (cKerSumZero ((n + 2) + (n + 2)) * (4 * K) ^ (2 * ((n + 2) + (n + 2)))
            * (κA * ((1 - v) * ellHat L (v : ℂ)))⁻¹ ^ ((n + 2) + (n + 2)) * momNorm P q ψ
        + (cKerSumZero ((n + 2) + (n + 2)) * (4 * K) ^ (2 * ((n + 2) + (n + 2)))
              * ((1 - s) / (1 - v)) ^ ((n + 2) + (n + 2)) * ζ
          + cKerSumZeroErr ((n + 2) + (n + 2)) * (L : ℝ) ^ ((n + 2) + (n + 2))
              * ((1 - s) / (1 - v)) ^ ((n + 2) + (n + 2))
              * FastDecayFlow.qqErr L (n + 1) (ellHat L ((u : ℝ) : ℂ)) K e δ))
        + Env * pr ^ ((1 : ℝ) / q) := by
  classical
  have hu0 : (0 : ℝ) ≤ u := hs0.trans hsu
  have hu1 : u < 1 := huv.trans_lt hv1
  have hℓ0 : (0 : ℝ) < ellHat L ((u : ℝ) : ℂ) := by
    have := half_le_ellHat_real L hL hu0 hu1; linarith
  have hbase : (0 : ℝ) < κA * ((1 - u) * ellHat L ((u : ℝ) : ℂ)) :=
    mul_pos hκA (mul_pos (by linarith) hℓ0)
  have hpw : (0 : ℝ) ≤ (κA * ((1 - u) * ellHat L ((u : ℝ) : ℂ)))⁻¹ ^ ((n + 2) + (n + 2)) :=
    pow_nonneg (inv_nonneg.2 hbase.le) _
  have hT0 : (fun A' : LoopArg L ((n + 2) + (n + 2)) → ℂ => QQ L ((u : ℝ) : ℂ) A') 0 = 0 :=
    FastDecayFlow.QQ_zero L (k := n + 1) _
  have hU0 : (fun A' : LoopArg L ((n + 2) + (n + 2)) → ℂ =>
      Uker L (xi2 E σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ) (QQ L ((u : ℝ) : ℂ) A')) 0 = 0 := by
    change Uker L (xi2 E σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
      (QQ L ((u : ℝ) : ℂ) (0 : LoopArg L ((n + 2) + (n + 2)) → ℂ)) = 0
    rw [FastDecayFlow.QQ_zero L (k := n + 1)]
    exact FastDecayFlow.Uker_zero (xi2 E σ) _ _
  have key := FastDecayFlow.momNorm_Uker_QQ_event_le (P := P) L hL hq hE σ hs0 hsu huv hv0
    hv1 hκA hK hζ he hδ (Ξ := measCore P Ξ) (A := A) (ψ := ψ) hψ0 hint
    (norm_apply_indicator_le hT0
      (g := fun ω =>
        (κA * ((1 - u) * ellHat L ((u : ℝ) : ℂ)))⁻¹ ^ ((n + 2) + (n + 2)) * ψ ω + ζ)
      (fun ω => add_nonneg (mul_nonneg hpw (hψ0 ω)) hζ) hGM)
    (fun ω hω => hAe ω (measCore_subset P Ξ hω))
    (fun ω hω => hAd ω (measCore_subset P Ξ hω)) a
  have heq : (fun ω => ‖Uker L (xi2 E σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
        (QQ L ((u : ℝ) : ℂ) (Set.indicator (measCore P Ξ) A ω)) a‖)
      = Set.indicator (measCore P Ξ) (fun ω =>
          ‖Uker L (xi2 E σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
            (QQ L ((u : ℝ) : ℂ) (A ω)) a‖) := by
    funext ω
    exact norm_apply_indicator_eq
      (T := fun A' : LoopArg L ((n + 2) + (n + 2)) → ℂ =>
        Uker L (xi2 E σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ) (QQ L ((u : ℝ) : ℂ) A'))
      hU0 A a ω
  rw [heq] at key
  have tail := momNorm_le_indicator_measCore_add_env (P := P) hq
    (Z := fun ω => ‖Uker L (xi2 E σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
      (QQ L ((u : ℝ) : ℂ) (A ω)) a‖)
    (by simpa only [abs_norm] using hZint) Ξ hEnv hpr
    (fun ω => by rw [abs_of_nonneg (norm_nonneg _)]; exact hZall ω) hPr
  linarith

end EventRestricted

/-! ### §5  The `Qop` half of the `hEnv…` slots

The `hEnv…` rows of `RBM.Gauss.rhs514QAt_of_kernel_inputs` ask for a size bound on
`Q_u ∘ T`, not on `T`.  Lemma 5.13 `RBM.SumZeroDyn.norm_Qop_le_of_fastDecay` is the reduction
to `T` itself: a tensor bounded by `M` and `(ℓ_u K, δ)`-fast-decaying has
`|Q_u ∘ T| ≤ (1 + (6e c K)^{m-1}) M + (2c)^{m-1} L^{m-1} δ`.  Written against the
normalisation `(κ_A (1-u) ℓ̂_u)^{-(n+2)}` that `RBM.Gauss.scale_eq_kappaA` identifies with
`A_u^{-(n+2)}`, that is exactly the shape of the `hGM` slot — and it is asked **only on the
event**, so it composes with §4 rather than re-introducing a `∀ ω` premise. -/

section EnvQop

variable {Ω : Type*} {L : ℕ}

/-- **The `hGM` slot of `RBM.FastDecayFlow.momNorm_Uker_Qop_event_le`, discharged on the
event.**  Off `Ξ` the truncated tensor is `0` and `Q_u` kills it, so the bound is free there;
on `Ξ` it is Lemma 5.13. -/
theorem hGM_Qop_of_event [NeZero L] (hL : 3 ≤ L) {n : ℕ} {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    {κA : ℝ} (hκA : 0 < κA) {K M δ : ℝ} (hK : 1 ≤ K) (hM : 0 ≤ M) (hδ : 0 ≤ δ)
    {Ξ : Set Ω} {A : Ω → LoopArg L (n + 2) → ℂ}
    (hAM : ∀ ω ∈ Ξ, ∀ b, ‖A ω b‖ ≤ M)
    (hAd : ∀ ω ∈ Ξ, FastDecay L (ellHat L ((u : ℝ) : ℂ) * K) δ (A ω))
    (ω : Ω) (b : LoopArg L (n + 2)) :
    ‖Qop L ((u : ℝ) : ℂ) (Set.indicator Ξ A ω) b‖
      ≤ (κA * ((1 - u) * ellHat L (u : ℂ)))⁻¹ ^ (n + 2)
          * ((κA * ((1 - u) * ellHat L (u : ℂ))) ^ (n + 2)
            * ((1 + (6 * Real.exp 1 * cTwo52 * K) ^ (n + 1)) * M))
        + (2 * cTwo52) ^ (n + 1) * (L : ℝ) ^ (n + 1) * δ := by
  classical
  have hℓ0 : (0 : ℝ) < ellHat L ((u : ℝ) : ℂ) := by
    have := half_le_ellHat_real L hL hu0 hu1; linarith
  have hbase : (0 : ℝ) < κA * ((1 - u) * ellHat L ((u : ℝ) : ℂ)) :=
    mul_pos hκA (mul_pos (by linarith) hℓ0)
  have hcancel : (κA * ((1 - u) * ellHat L ((u : ℝ) : ℂ)))⁻¹ ^ (n + 2)
      * ((κA * ((1 - u) * ellHat L ((u : ℝ) : ℂ))) ^ (n + 2)
        * ((1 + (6 * Real.exp 1 * cTwo52 * K) ^ (n + 1)) * M))
      = (1 + (6 * Real.exp 1 * cTwo52 * K) ^ (n + 1)) * M := by
    rw [inv_pow, inv_mul_cancel_left₀ (pow_ne_zero _ (ne_of_gt hbase))]
  rw [hcancel]
  by_cases hω : ω ∈ Ξ
  · rw [Set.indicator_of_mem hω]
    exact SumZeroDyn.norm_Qop_le_of_fastDecay L hL hu0 hu1 hK hM hδ (hAM ω hω) (hAd ω hω) b
  · rw [Set.indicator_of_notMem hω, FastDecayFlow.Qop_zero L]
    have h1 : (0 : ℝ) ≤ (1 + (6 * Real.exp 1 * cTwo52 * K) ^ (n + 1)) * M := by
      have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
      have hc := cTwo52_pos
      have : (0 : ℝ) ≤ (6 * Real.exp 1 * cTwo52 * K) ^ (n + 1) := by positivity
      nlinarith
    have h2 : (0 : ℝ) ≤ (2 * cTwo52) ^ (n + 1) * (L : ℝ) ^ (n + 1) * δ := by
      have hc := cTwo52_pos
      positivity
    simpa using by linarith

end EnvQop

/-! ### §6  Satisfiability, and the chain closed at the model

Two things have to be true for §4 to have content.

* The event must not be empty: §2's `RBM.Gauss.nonempty_lkGoodM` rules that out, by quoting
  T220's `RBM.FastDecayFlow.highProb_lkGood` and `RBM.FastDecayFlow.nonempty_of_highProb` —
  nothing is re-proved here.
* The Markov price `Env · P(Ξᶜ)^{1/q}` must actually be small.  T218's
  `RBM.Gauss.eventually_env_mul_prob_rpow_le` says it is, for every polynomial envelope, in
  the quantifier order the moment route uses (`q` fixed, then `N → ∞`). -/

section Model

open RBM.MomentDuhamel

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {X : Sample B} {E : ℝ} {s t : ℕ → ℝ}

/-- **The witness that §4 is not vacuous at the model event.**  All three clauses at once, for
the good event of (5.75): it holds with high probability, its measurable core is a subset of
it (so every `∀ ω ∈ Ξ` premise of §4 survives), and the core is eventually non-empty. -/
theorem lkGoodM_witness [IsProbabilityMeasure B.P] (hdec : LKDecay X E s t) {m : ℕ}
    (hm : 1 ≤ m) {τ τ₁ D : ℝ} (hτ : 0 < τ) (hτ₁ : 0 < τ₁) (hD : 0 < D) :
    HighProb B.P (FastDecayFlow.lkGood X E s t m τ τ₁ D)
    ∧ HighProb B.P (lkGoodM X E s t m τ τ₁ D)
    ∧ (∀ N, lkGoodM X E s t m τ τ₁ D N ⊆ FastDecayFlow.lkGood X E s t m τ τ₁ D N)
    ∧ ∀ᶠ N : ℕ in atTop, (lkGoodM X E s t m τ τ₁ D N).Nonempty :=
  ⟨FastDecayFlow.highProb_lkGood hdec hm hτ hτ₁ hD,
    highProb_lkGoodM hdec hm hτ hτ₁ hD,
    fun N => lkGoodM_subset X E s t m τ τ₁ D N,
    nonempty_lkGoodM hdec hm hτ hτ₁ hD⟩

/-- **The Markov price of the split is eventually negligible**, at the good event of (5.75).
`RBM.Gauss.eventually_env_mul_prob_rpow_le` (T218) applied to
`RBM.FastDecayFlow.highProb_lkGood`; the quantifier order is `q`, `D` first, then `N → ∞`. -/
theorem eventually_env_mul_lkGood_le [IsProbabilityMeasure B.P] (hdec : LKDecay X E s t)
    {m : ℕ} (hm : 1 ≤ m) {τ τ₁ D₀ : ℝ} (hτ : 0 < τ) (hτ₁ : 0 < τ₁) (hD₀ : 0 < D₀) {q : ℕ}
    (hq : q ≠ 0) {Env : ℕ → ℝ} {Cenv : ℝ} (hCenv : 0 ≤ Cenv)
    (hEnvle : ∀ᶠ N : ℕ in atTop, Env N ≤ (N : ℝ) ^ Cenv) {D : ℝ} (hD : 0 < D) :
    ∀ᶠ N : ℕ in atTop,
      Env N * ((B.P (FastDecayFlow.lkGood X E s t m τ τ₁ D₀ N)ᶜ).toReal) ^ ((1 : ℝ) / q)
        ≤ (N : ℝ) ^ (-D) :=
  eventually_env_mul_prob_rpow_le hq (FastDecayFlow.highProb_lkGood hdec hm hτ hτ₁ hD₀)
    hCenv hEnvle hD

/-- **(7.16) in moment form for `Q_u ∘ (L-K)_u`, with (7.13) a theorem and the conclusion
about the untruncated tensor.**

This is the model-level endpoint of the ticket.  Compare
`RBM.FastDecayFlow.momNorm_Uker_Qop_lkT_le` (T220, §12): there the conclusion is about
`1_Ξ (L-K)` and the inclusion `Ξ ⊆ lkGood` is a hypothesis; here the event **is** the good
event of (5.75), its (7.13) is supplied by `RBM.FastDecayFlow.fastDecay_lkT_of_mem_lkGood`,
and the passage back to `(L-K)` itself is paid for by `Env · P(lkGoodᶜ)^{1/q}`, which
`RBM.Gauss.eventually_env_mul_lkGood_le` shows is eventually below any `N^{-D}`.

No hypothesis of this theorem is a decay statement quantified over all `ω`. -/
theorem momNorm_Uker_Qop_lkT_untrunc_le [IsProbabilityMeasure B.P] (hE : |E| ≤ 2) {q n N : ℕ}
    (hq : q ≠ 0) (σ : Fin (n + 2) → Bool) {u v : ℝ} (hs0 : 0 ≤ s N) (hsu : s N ≤ u)
    (hut : u ≤ t N) (huv : u ≤ v) (hv0 : 0 ≤ v) (hv1 : v < 1) {κA : ℝ} (hκA : 0 < κA)
    {τ τ₁ D M ζ : ℝ} (hτK : 1 ≤ (N : ℝ) ^ τ) (hM : 0 ≤ M) (hζ : 0 ≤ ζ)
    {ψ : Ω → ℝ} (hψ0 : ∀ ω, 0 ≤ ψ ω) (hint : Integrable (fun ω => ψ ω ^ q) B.P)
    (hGM : ∀ ω b, ‖Qop (B.L N) ((u : ℝ) : ℂ) (lkT X E N u ω σ) b‖
      ≤ (κA * ((1 - u) * ellHat (B.L N) (u : ℂ)))⁻¹ ^ (n + 2) * ψ ω + ζ)
    (hAM : ∀ ω ∈ FastDecayFlow.lkGood X E s t (n + 2) τ τ₁ D N, ∀ b,
      ‖lkT X E N u ω σ b‖ ≤ M)
    (a : LoopArg (B.L N) (n + 2)) {Env pr : ℝ} (hEnv : 0 ≤ Env) (hpr : 0 ≤ pr)
    (hZall : ∀ ω, ‖Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
      (Qop (B.L N) ((u : ℝ) : ℂ) (lkT X E N u ω σ)) a‖ ≤ Env)
    (hZint : Integrable (fun ω =>
      ‖Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
        (Qop (B.L N) ((u : ℝ) : ℂ) (lkT X E N u ω σ)) a‖ ^ q) B.P)
    (hPr : (B.P (FastDecayFlow.lkGood X E s t (n + 2) τ τ₁ D N)ᶜ).toReal ≤ pr) :
    momNorm B.P q (fun ω =>
        ‖Uker (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
          (Qop (B.L N) ((u : ℝ) : ℂ) (lkT X E N u ω σ)) a‖)
      ≤ (cKerSumZero (n + 2) * ((N : ℝ) ^ τ) ^ (2 * (n + 2))
            * (κA * ((1 - v) * ellHat (B.L N) (v : ℂ)))⁻¹ ^ (n + 2) * momNorm B.P q ψ
        + (cKerSumZero (n + 2) * ((N : ℝ) ^ τ) ^ (2 * (n + 2))
              * ((1 - s N) / (1 - v)) ^ (n + 2) * ζ
          + cKerSumZeroErr (n + 2) * (B.L N : ℝ) ^ (n + 2) * ((1 - s N) / (1 - v)) ^ (n + 2)
              * FastDecayFlow.qopErr1 (B.L N) n ((N : ℝ) ^ τ) M
                  ((N : ℝ) ^ τ₁ * (N : ℝ) ^ (-D))))
        + Env * pr ^ ((1 : ℝ) / q) :=
  momNorm_Uker_Qop_event_untrunc_le (B.L N) (B.three_le_L N) hq hE σ hs0 hsu huv hv0 hv1 hκA
    hτK hM hζ (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _)
      (Real.rpow_nonneg (Nat.cast_nonneg N) _)) hψ0 hint hGM hAM
    (fun _ hω => FastDecayFlow.fastDecay_lkT_of_mem_lkGood hsu hut hω σ) a hEnv hpr hZall
    hZint hPr

end Model

/-! ### §7  The `MeasurableSet` premise of T218's good-event Minkowski, removed

`RBM.Gauss.momNorm_norm_lkT_le_of_event` and `RBM.Gauss.momNorm_norm_lkT_le_of_hyp`
(T218, the returning half of (5.101) on the moment route) carry a named hypothesis
`hΞm : MeasurableSet Ξ`.  Their event is the one where (5.75) and (5.76) hold, i.e. an
intersection over the uncountable window, so `hΞm` had no producer.  §1 removes it: neither
theorem's *conclusion* mentions `Ξ`, so replacing `Ξ` by its measurable core changes nothing
on the right and weakens nothing on the left. -/

section NoMeas

open RBM.MomentDuhamel

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- **`RBM.Gauss.momNorm_norm_lkT_le_of_event` with `MeasurableSet Ξ` deleted.** -/
theorem momNorm_norm_lkT_le_of_event_nomeas [IsProbabilityMeasure B.P] (X : Sample B) {E : ℝ}
    (hE : |E| < 2) {q : ℕ} (hq : q ≠ 0) {n : ℕ} (hW : SumZeroDyn.WardP X E n)
    {N : ℕ} {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1)
    {σ : Fin (n + 2) → Bool} (hqg : SumZeroDyn.QGood σ) (a : LoopArg (B.L N) (n + 2))
    {K φ δ : ℝ} (hK : 0 < K) (hφ : 0 ≤ φ) (hδ : 0 ≤ δ)
    {Ξ : Set Ω}
    (hΞ1 : ∀ ω ∈ Ξ, X.xiLK E N v ω (n + 1) ≤ K * φ)
    (hΞ2 : ∀ ω ∈ Ξ, ∀ (ρ : Fin (n + 1) → Bool) b,
      X.lkErr E N v ω (LoopData.idx (ρ, b)) * SumZeroDyn.farInd (B.L N) (B.ell N v * K) b ≤ δ)
    {Env pr : ℝ} (hEnv : 0 ≤ Env) (hpr : 0 ≤ pr)
    (hall : ∀ ω, ‖SumZeroDyn.lkT X E N v ω σ a‖ ≤ Env)
    (hPr : (B.P Ξᶜ).toReal ≤ pr)
    (hQint : Integrable
      (fun ω => ‖Qop (B.L N) ((v : ℝ) : ℂ) (SumZeroDyn.lkT X E N v ω σ) a‖ ^ q) B.P)
    (hAint : Integrable (fun ω => |‖SumZeroDyn.lkT X E N v ω σ a‖| ^ q) B.P) :
    momNorm B.P q (fun ω => ‖SumZeroDyn.lkT X E N v ω σ a‖)
      ≤ momNorm B.P q
          (fun ω => ‖Qop (B.L N) ((v : ℝ) : ℂ) (SumZeroDyn.lkT X E N v ω σ) a‖)
        + pHalfBound B E N v n K φ δ + Env * pr ^ ((1 : ℝ) / q) :=
  momNorm_norm_lkT_le_of_event X hE hq hW hv0 hv1 hqg a hK hφ hδ
    (measurableSet_measCore B.P Ξ)
    (fun ω hω => hΞ1 ω (measCore_subset B.P Ξ hω))
    (fun ω hω => hΞ2 ω (measCore_subset B.P Ξ hω)) hEnv hpr hall
    (by rw [measureReal_compl_measCore]; exact hPr) hQint hAint

/-- **`RBM.Gauss.momNorm_norm_lkT_le_of_hyp` with `MeasurableSet Ξ` deleted.** -/
theorem momNorm_norm_lkT_le_of_hyp_nomeas [IsProbabilityMeasure B.P] {X : Sample B} {E : ℝ}
    (hE : |E| < 2) {s t : ℕ → ℝ} {n : ℕ} (H : Hyp X E s t n) (hQint : QIntegrable X E s t n)
    {p : ℕ} (hp : 1 ≤ p) (hW : SumZeroDyn.WardP X E n)
    {N : ℕ} {v : ℝ} (hsv : s N ≤ v) (hvt : v ≤ t N) (hv0 : 0 ≤ v) (hv1 : v < 1)
    {σ : Fin (n + 2) → Bool} (hqg : SumZeroDyn.QGood σ) (a : LoopArg (B.L N) (n + 2))
    {K φ δ : ℝ} (hK : 0 < K) (hφ : 0 ≤ φ) (hδ : 0 ≤ δ)
    {Ξ : Set Ω}
    (hΞ1 : ∀ ω ∈ Ξ, X.xiLK E N v ω (n + 1) ≤ K * φ)
    (hΞ2 : ∀ ω ∈ Ξ, ∀ (ρ : Fin (n + 1) → Bool) b,
      X.lkErr E N v ω (LoopData.idx (ρ, b)) * SumZeroDyn.farInd (B.L N) (B.ell N v * K) b ≤ δ)
    {Env pr : ℝ} (hEnv : 0 ≤ Env) (hpr : 0 ≤ pr)
    (hall : ∀ ω, ‖SumZeroDyn.lkT X E N v ω σ a‖ ≤ Env)
    (hPr : (B.P Ξᶜ).toReal ≤ pr) :
    momNorm B.P (2 * p) (fun ω => ‖SumZeroDyn.lkT X E N v ω σ a‖)
      ≤ momNorm B.P (2 * p)
          (fun ω => ‖Qop (B.L N) ((v : ℝ) : ℂ) (SumZeroDyn.lkT X E N v ω σ) a‖)
        + pHalfBound B E N v n K φ δ + Env * pr ^ ((1 : ℝ) / (2 * p : ℕ)) :=
  momNorm_norm_lkT_le_of_hyp hE H hQint hp hW hsv hvt hv0 hv1 hqg a hK hφ hδ
    (measurableSet_measCore B.P Ξ)
    (fun ω hω => hΞ1 ω (measCore_subset B.P Ξ hω))
    (fun ω hω => hΞ2 ω (measCore_subset B.P Ξ hω)) hEnv hpr hall
    (by rw [measureReal_compl_measCore]; exact hPr)

end NoMeas

end RBM.Gauss


