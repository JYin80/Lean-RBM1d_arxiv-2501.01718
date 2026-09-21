/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.DominationHolder
import RBM1D.Gauss.FlowHolder
import RBM1D.Gauss.DistEq
import RBM1D.Gauss.Lemma41FlowGauss
import RBM1D.Gauss.TraceMoment

/-!
# The two remaining fields of `RBM.Step1.Hyp` for the Gaussian model — T116

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, §5.1 (pp. 51–52).

`RBM.Step1.Hyp` (`RBM1D/Hierarchy/Step1.lean`) has four fields.  Two already have Gaussian
producers: `scaling` is `RBM.Gauss.loopScaling_gauss` (T111) and `lemma41` is
`RBM.Gauss.lemma41Flow` (T108).  This file supplies `cont` and analyses `lift`.

## `cont` — done, unconditionally

`RBM.Gauss.cont_gauss`.  The event is **all of `Ω`**: for the Gaussian flow
`H_u = √u X`, `z_u = E + (1-u) m`, the map `u ↦ ‖G_u - m‖_max` is continuous on `[s_N, t_N]`
for *every* sample, because
```
‖G_u - G_{u'}‖ ≤ η_u^{-1}(|√u - √u'| ‖X‖ + |u-u'|) η_{u'}^{-1}
              ≤ η_{t_N}^{-2}(‖X‖+1) |u - u'|^{1/2}      (`norm_green_flow_sub_le_sqrt`)
```
on `[s_N, t_N] ⊆ [0, t_N]`, `t_N < 1`.  No probability, no exceptional set, and in particular
`‖X‖ ≺ 1` is *not* needed — the constant is random but finite for each `ω`.

## `lift` — **not** bypassable the way `Lemma41Flow` was

T108 removed the time net from `RBM.Step1.Lemma41Flow` because that statement is a transfer
between two dominations *both already uniform in the time*, so the time could be carried inside
the index set.  `RBM.Step1.NetLift` is different: `RBM.StochDom` puts the union over the index
set **inside** the probability (`RBM.badSet`), so its hypothesis — a bound along every time
*sequence* — controls `P(A_{u(N)})` for one time per `N`, while its conclusion needs
`P(⋃_{u ∈ [s_N,t_N]} A_u)`.  Exactly one half of that gap is free, and this file isolates it:

* `eventually_forall_measure_slice_le` — **free**: a choice of one time per `N` *is* a sequence,
  so the failure bound holds simultaneously for every `N`-dependent choice `θ(N) : W(N) → [s,t]`.
  (A `by_contra` plus `Classical.choice`; no continuity, no net.)
* `stochDom_reindex_of_forall_seq` — the union over `W(N)` *inside* the probability, at the cost
  of `#W(N) ≤ N^C` (`RBM.StochDom.of_forall_le`).
* `stochDom_of_forall_seq_relaxed` — the uncountable union, by the `N^{-(A+1)}`-net of (5.46)
  (`RBM.Gauss.netTime`, `netTimeIcc`) plus `RBM.Gauss.stochDom_of_subset_highProb` (T101).
* `netLift_of_modulus_hp`, `netLift_of_relaxed` — the two `RBM.Step1.NetLift` producers.

`netLift_of_relaxed` allows the net points to carry a **relaxed** family `(ξ', ζ')`.  That is
not a luxury: the family of (5.8) carries the indicator `1(‖G_u‖_max ≤ 2)`, which is *not*
continuous in `u`, so `ξ` at `u` is never controlled by `ξ` at a net point — `‖G_{u'}‖_max` is
only `≤ 2 + o(1)`.  This is the gap that `RBM1D/Hierarchy/Step1.lean` already records in its
deviations ("the paper's net argument implicitly uses Lemma 5.1 with threshold `2 + o(1)` at the
net points").  `netLift_of_relaxed` reduces `lift` to exactly that: a `≺`-bound **along time
sequences** for the family with the raised threshold.  Producing that bound (a relaxed-threshold
rerun of Lemma 5.1) is not done here — see "What is not done".

## Main results

* `continuousOn_of_sqrt_modulus`, `self_le_sqrt_of_le_one` — generic real analysis.
* `norm_green_flow_sub_le_sqrt`, `abs_llMax_sub_le_sqrt`, `continuousOn_llMax`,
  `highProb_norm_Xmat_le`, `cont_gauss` — the Gaussian side.
* `eventually_forall_measure_slice_le`, `stochDom_reindex_of_forall_seq`, `netTimeIcc`,
  `stochDom_of_forall_seq_relaxed`, `netLift_of_modulus_hp`, `netLift_of_relaxed` — the
  `NetLift` machinery (generic in `(Ω, P)`; nothing Gaussian).
* `step1Hyp_gauss` — a complete `RBM.Step1.Hyp (sample d) E s t`, with `lift`, (4.2) and (4.3)
  along the flow as its only inputs.

## What was not done in T116, and is done below (T125)

`lift` itself.  Closing it needed, on top of `netLift_of_relaxed`: (i) a modulus in `u` for
`‖L_{u,σ,a}‖` (a telescoping estimate for `RBM.gloop`, not available — `Gauss/Envelope.lean`
only has the envelope `‖L‖ ≤ η_t^{-n} W^{-n+1}` and the difference against a *fixed* kernel);
(ii) the slow variation `ζ(u') ≤ 2 ζ(u)` of `RBM.Step1.aprioriRhs`, which for the exponent
`n - 1` needs the net spacing below `c_n (1 - t_N)` and hence a regime hypothesis
(the `Φ`-version is `RBM.Gauss.step1Phi_eq` and the slow-variation section of
`Gauss/Lemma41FlowGauss.lean`); (iii) the polynomial lower bound `N^{-B} ≤ ζ`, i.e.
`W ℓ_u η_u ≤ N^{B/(n-1)}`; and (iv) Lemma 5.1 at the threshold `2 + o(1)`.
All four are supplied in the section "T125: `lift` discharged" at the end of this file; see
`RBM.Gauss.netLift_gauss` and `RBM.Gauss.step1Hyp_gauss_of_regime`.

## Deviations from the paper

See `docs/paper-deltas.md`: the indicator of (5.8) is not continuous in `u`, so the paper's
one-line net argument on p. 51 is *not* the net argument for the family it is applied to; the
faithful statement is `netLift_of_relaxed`, whose input is Lemma 5.1 at the raised threshold.
-/

namespace RBM.Gauss

open Filter MeasureTheory

open scoped Matrix.Norms.L2Operator

/-! ### A continuity criterion from a square-root modulus -/

/-- A function with a uniform `√`-modulus on a set is continuous on that set. -/
theorem continuousOn_of_sqrt_modulus {f : ℝ → ℝ} {S : Set ℝ} {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ u ∈ S, ∀ u' ∈ S, |f u - f u'| ≤ K * Real.sqrt |u - u'|) : ContinuousOn f S := by
  rw [Metric.continuousOn_iff]
  intro b hb ε hε
  refine ⟨(ε / (K + 1)) ^ 2, by positivity, fun a ha hab => ?_⟩
  have hKε : 0 < ε / (K + 1) := by positivity
  have hs : Real.sqrt |a - b| < ε / (K + 1) := by
    have h1 : Real.sqrt |a - b| < Real.sqrt ((ε / (K + 1)) ^ 2) :=
      Real.sqrt_lt_sqrt (abs_nonneg _) (by rwa [Real.dist_eq] at hab)
    rwa [Real.sqrt_sq hKε.le] at h1
  have hfb := h a ha b hb
  rw [Real.dist_eq]
  rcases eq_or_lt_of_le hK with hK0 | hK0
  · calc |f a - f b| ≤ K * Real.sqrt |a - b| := hfb
      _ = 0 := by rw [← hK0]; ring
      _ < ε := hε
  · calc |f a - f b| ≤ K * Real.sqrt |a - b| := hfb
      _ < K * (ε / (K + 1)) := by exact mul_lt_mul_of_pos_left hs hK0
      _ < ε := by
          rw [mul_div_assoc'] at *
          rw [div_lt_iff₀ (by linarith)]
          nlinarith

/-! ### `x ≤ √x` on `[0, 1]` -/

/-- `x ≤ √x` for `0 ≤ x ≤ 1`. -/
theorem self_le_sqrt_of_le_one {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : x ≤ Real.sqrt x :=
  (Real.le_sqrt hx0 hx0).2 (by nlinarith)

/-! ### The field `cont`: continuity of `u ↦ ‖G_u - m‖_max`, for **every** sample -/

variable {d : Dims}

/-- **The `√`-modulus of the resolvent of the flow on `[s_N, t_N]`, pathwise.**  Both the matrix
and the spectral parameter move with `u`: `‖H_u - H_{u'}‖ = |√u - √u'| ‖X‖`,
`|z_u - z_{u'}| = |u - u'|`, and `‖G‖ ≤ η_u^{-1} ≤ η_{t}^{-1}` on `[s, t]`.  Together with
`|√u - √u'| ≤ √|u-u'|` and `|u - u'| ≤ √|u-u'|` (the interval is inside `[0,1]`) this is a
Hölder-`1/2` modulus with the random constant `η_t^{-2}(‖X‖+1)`. -/
theorem norm_green_flow_sub_le_sqrt (d : Dims) (N : ℕ) {E : ℝ} (hE : |E| < 2) {s t : ℝ}
    (hs0 : 0 ≤ s) (ht1 : t < 1) (ω : Ω d) {u u' : ℝ} (hu : u ∈ Set.Icc s t)
    (hu' : u' ∈ Set.Icc s t) :
    ‖green (Hflow d N u ω) (zt E u) - green (Hflow d N u' ω) (zt E u')‖
      ≤ ((etaT E t)⁻¹ * (etaT E t)⁻¹ * (‖Xmat d N ω‖ + 1)) * Real.sqrt |u - u'| := by
  have hηt : 0 < etaT E t := etaT_pos_of_lt_one' hE ht1
  have hu1 : u < 1 := lt_of_le_of_lt hu.2 ht1
  have hu'1 : u' < 1 := lt_of_le_of_lt hu'.2 ht1
  have hηu : etaT E t ≤ etaT E u := etaT_le_of_le hE hu.2
  have hηu' : etaT E t ≤ etaT E u' := etaT_le_of_le hE hu'.2
  have hiu : (etaT E u)⁻¹ ≤ (etaT E t)⁻¹ := inv_anti₀ hηt hηu
  have hiu' : (etaT E u')⁻¹ ≤ (etaT E t)⁻¹ := inv_anti₀ hηt hηu'
  have hiu0 : 0 ≤ (etaT E u)⁻¹ := inv_nonneg.2 (le_of_lt (etaT_pos_of_lt_one' hE hu1))
  have hiu'0 : 0 ≤ (etaT E u')⁻¹ := inv_nonneg.2 (le_of_lt (etaT_pos_of_lt_one' hE hu'1))
  have hX : (0 : ℝ) ≤ ‖Xmat d N ω‖ := norm_nonneg _
  have h1 : |Real.sqrt u - Real.sqrt u'| ≤ Real.sqrt |u - u'| := Gauss.abs_sqrt_sub_sqrt_le u u'
  have hdiff : |u - u'| ≤ 1 := by
    rcases le_total u u' with h | h
    · rw [abs_of_nonpos (by linarith)]
      have := hu.1; have := hu'.2; linarith
    · rw [abs_of_nonneg (by linarith)]
      have := hu'.1; have := hu.2; linarith
  have h2 : |u - u'| ≤ Real.sqrt |u - u'| := self_le_sqrt_of_le_one (abs_nonneg _) hdiff
  have hsq0 : (0 : ℝ) ≤ Real.sqrt |u - u'| := Real.sqrt_nonneg _
  refine (norm_green_flow_sub_le d N hE hu1 hu'1 ω).trans ?_
  have hmid : |Real.sqrt u - Real.sqrt u'| * ‖Xmat d N ω‖ + |u - u'|
      ≤ Real.sqrt |u - u'| * (‖Xmat d N ω‖ + 1) := by
    have := mul_le_mul_of_nonneg_right h1 hX
    nlinarith
  calc (etaT E u)⁻¹ * (|Real.sqrt u - Real.sqrt u'| * ‖Xmat d N ω‖ + |u - u'|) * (etaT E u')⁻¹
      ≤ (etaT E t)⁻¹ * (Real.sqrt |u - u'| * (‖Xmat d N ω‖ + 1)) * (etaT E t)⁻¹ := by
        have hmid0 : (0 : ℝ) ≤ |Real.sqrt u - Real.sqrt u'| * ‖Xmat d N ω‖ + |u - u'| := by
          positivity
        gcongr
    _ = ((etaT E t)⁻¹ * (etaT E t)⁻¹ * (‖Xmat d N ω‖ + 1)) * Real.sqrt |u - u'| := by ring

/-- The same `√`-modulus for `‖G_u - m‖_max`, entrywise. -/
theorem abs_llMax_sub_le_sqrt (d : Dims) (N : ℕ) {E : ℝ} (hE : |E| < 2) {s t : ℝ}
    (hs0 : 0 ≤ s) (ht1 : t < 1) (ω : Ω d) {u u' : ℝ} (hu : u ∈ Set.Icc s t)
    (hu' : u' ∈ Set.Icc s t) :
    |Step1.llMax (sample d) E N u ω - Step1.llMax (sample d) E N u' ω|
      ≤ ((etaT E t)⁻¹ * (etaT E t)⁻¹ * (‖Xmat d N ω‖ + 1)) * Real.sqrt |u - u'| :=
  (abs_llMax_sub_le d N E u u' ω).trans (norm_green_flow_sub_le_sqrt d N hE hs0 ht1 ω hu hu')

/-- **`u ↦ ‖G_u - m‖_max` is continuous on `[s_N, t_N]` for every sample `ω`.**  No probability
is involved: the Gaussian flow `H_u = √u X` and the spectral parameter `z_u = E + (1-u) m` are
continuous in `u`, and the resolvent is Lipschitz in both as long as `u ≤ t_N < 1`. -/
theorem continuousOn_llMax (d : Dims) (N : ℕ) {E : ℝ} (hE : |E| < 2) {s t : ℝ} (hs0 : 0 ≤ s)
    (ht1 : t < 1) (ω : Ω d) :
    ContinuousOn (fun u => Step1.llMax (sample d) E N u ω) (Set.Icc s t) := by
  have hηt : 0 < etaT E t := etaT_pos_of_lt_one' hE ht1
  refine continuousOn_of_sqrt_modulus (K := (etaT E t)⁻¹ * (etaT E t)⁻¹ * (‖Xmat d N ω‖ + 1))
    (by positivity) fun u hu u' hu' => abs_llMax_sub_le_sqrt d N hE hs0 ht1 ω hu hu'

/-- **The high-probability event on which the Hölder constant of the flow is deterministic**:
`‖X‖ ≤ N`.  This is `RBM.Gauss.stochDom_norm_Xmat_gauss` (`‖X‖ ≺ 1`, T109, unconditional) at
`τ = 1`; on it the modulus of `norm_green_flow_sub_le_sqrt` becomes
`η_t^{-2}(N+1)|u-u'|^{1/2}`, which is the `Ξ` that `netLift_of_relaxed` wants. -/
theorem highProb_norm_Xmat_le (d : Dims) :
    HighProb (P d) (fun N => {ω | ‖Xmat d N ω‖ ≤ (N : ℝ)}) := by
  refine ((stochDom_norm_Xmat_gauss d).highProb one_pos).mono
    (Eventually.of_forall fun N ω hω => ?_)
  have h := hω ()
  simpa [Real.rpow_one] using h

/-- **The field `RBM.Step1.Hyp.cont` for the Gaussian model, unconditionally.**  The event is
all of `Ω`: continuity in the time holds for every sample, so no exceptional set is needed. -/
theorem cont_gauss (d : Dims) {E : ℝ} (hE : |E| < 2) {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N)
    (ht1 : ∀ N, t N < 1) :
    HighProb (P d) (fun N => {ω | ContinuousOn
      (fun u => Step1.llMax (sample d) E N u ω) (Set.Icc (s N) (t N))}) := by
  intro D _
  filter_upwards with N
  have huniv : {ω : Ω d | ContinuousOn
      (fun u => Step1.llMax (sample d) E N u ω) (Set.Icc (s N) (t N))} = Set.univ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact continuousOn_llMax d N hE (hs0 N) (ht1 N) ω
  rw [huniv, Set.compl_univ, measure_empty]
  exact zero_le

/-! ### `lift`: what a bound along every time sequence does and does not give -/

section NetLift

variable {Ωb : Type*} [MeasurableSpace Ωb] {P : Measure Ωb} {s t : ℕ → ℝ}

/-- **The half of `RBM.Step1.NetLift` that is free.**  A `≺`-bound along *every* time sequence
`u(N) ∈ [s_N, t_N]` already gives the failure bound **uniformly over an `N`-dependent choice of
times**: for any family of maps `θ(N) : W(N) → [s_N, t_N]`, eventually in `N` *every* `θ(N,w)`
obeys the failure bound at level `D`.

This is the exact analogue of the T108 observation ("the time may be carried inside the index
set"): a choice of one time per `N` *is* a sequence, so no net and no continuity are needed.
What is *not* free is the union over `w` **inside** the probability — that is
`RBM.StochDom.of_forall_le` and costs a polynomial bound on `#W(N)`; and the union over the
**uncountably many** `u ∈ [s_N, t_N]` inside the probability, which is the actual content of
`RBM.Step1.NetLift`. -/
theorem eventually_forall_measure_slice_le {V W : ℕ → Type*}
    {ξ ζ : ∀ N, RBM.TimeIcc s t N × V N → Ωb → ℝ} (hst : ∀ N, s N ≤ t N)
    (h : ∀ u : ∀ N, RBM.TimeIcc s t N,
      StochDom P (fun N v ω => ξ N (u N, v) ω) (fun N v ω => ζ N (u N, v) ω))
    (θ : ∀ N, W N → RBM.TimeIcc s t N) {τ : ℝ} (hτ : 0 < τ) {D : ℝ} (hD : 0 < D) :
    ∀ᶠ N : ℕ in atTop, ∀ w : W N,
      P {ω | ∃ v : V N, (N : ℝ) ^ τ * ζ N (θ N w, v) ω < ξ N (θ N w, v) ω}
        ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
  classical
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  -- the choice of a bad time for each bad `N`
  set bad : ℕ → Prop := fun N => ∃ w : W N,
    ¬ (P {ω | ∃ v : V N, (N : ℝ) ^ τ * ζ N (θ N w, v) ω < ξ N (θ N w, v) ω}
      ≤ ENNReal.ofReal ((N : ℝ) ^ (-D))) with hbad_def
  have hcon' : ∃ᶠ N : ℕ in atTop, bad N := by
    refine hcon.mono fun N hN => ?_
    simpa only [hbad_def, not_forall] using hN
  set u : ∀ N, RBM.TimeIcc s t N := fun N =>
    if hN : bad N then θ N hN.choose else ⟨s N, le_rfl, hst N⟩ with hu_def
  have hseq := h u τ hτ D hD
  obtain ⟨N, hNbad, hNgood⟩ := (hcon'.and_eventually hseq).exists
  have huN : u N = θ N hNbad.choose := by rw [hu_def]; exact dite_eq_left hNbad
  refine hNbad.choose_spec ?_
  rw [← huN]
  exact hNgood

/-- **The union bound over an `N`-dependent, polynomially small set of times.**  Combining
`eventually_forall_measure_slice_le` (free) with the union bound `RBM.StochDom.of_forall_le`
(costs `#W(N) ≤ N^C`): a `≺`-bound along every time sequence gives a genuine `≺`-bound for the
family reindexed by `θ(N) : W(N) → [s_N, t_N]`, *with the union over `W(N)` inside the
probability*. -/
theorem stochDom_reindex_of_forall_seq {V W : ℕ → Type*} [∀ N, Fintype (W N)]
    {ξ ζ : ∀ N, RBM.TimeIcc s t N × V N → Ωb → ℝ} (hst : ∀ N, s N ≤ t N)
    (h : ∀ u : ∀ N, RBM.TimeIcc s t N,
      StochDom P (fun N v ω => ξ N (u N, v) ω) (fun N v ω => ζ N (u N, v) ω))
    (θ : ∀ N, W N → RBM.TimeIcc s t N) {C : ℝ} (hC : 0 ≤ C)
    (hcard : ∀ᶠ N : ℕ in atTop, (Fintype.card (W N) : ℝ) ≤ (N : ℝ) ^ C) :
    StochDom P (fun N (p : W N × V N) ω => ξ N (θ N p.1, p.2) ω)
      (fun N p ω => ζ N (θ N p.1, p.2) ω) := by
  intro τ hτ D hD
  filter_upwards [hcard, eventually_forall_measure_slice_le hst h θ hτ (by linarith : 0 < D + C),
    eventually_ge_atTop 1] with N hcardN hslice hN1
  have hp : (0 : ℝ) ≤ (N : ℝ) ^ (-(D + C)) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hset : badSet (fun N (p : W N × V N) ω => ξ N (θ N p.1, p.2) ω)
      (fun N p ω => ζ N (θ N p.1, p.2) ω) τ N
      = ⋃ w : W N, {ω | ∃ v : V N, (N : ℝ) ^ τ * ζ N (θ N w, v) ω < ξ N (θ N w, v) ω} := by
    ext ω
    simp only [badSet, Set.mem_ofPred_eq, Set.mem_iUnion, Prod.exists]
  calc P (badSet (fun N (p : W N × V N) ω => ξ N (θ N p.1, p.2) ω)
          (fun N p ω => ζ N (θ N p.1, p.2) ω) τ N)
      ≤ ∑ w : W N, P {ω | ∃ v : V N, (N : ℝ) ^ τ * ζ N (θ N w, v) ω < ξ N (θ N w, v) ω} := by
        rw [hset]; exact measure_iUnion_fintype_le P _
    _ ≤ ∑ _w : W N, ENNReal.ofReal ((N : ℝ) ^ (-(D + C))) :=
        Finset.sum_le_sum fun w _ => hslice w
    _ = ENNReal.ofReal (Fintype.card (W N) * (N : ℝ) ^ (-(D + C))) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ C * (N : ℝ) ^ (-(D + C))) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcardN hp)
    _ = ENNReal.ofReal ((N : ℝ) ^ (-D)) := by rw [rpow_mul_rpow_neg_add hN1]

/-- The `k`-th net point of `[s_N, t_N]`, as an element of `RBM.TimeIcc s t N`. -/
noncomputable def netTimeIcc {s t : ℕ → ℝ} (hst : ∀ N, s N ≤ t N) {T : ℝ} (hT : 0 ≤ T) (A : ℝ)
    (N : ℕ) (k : Fin (netSize A N + 1)) : RBM.TimeIcc s t N :=
  ⟨netTime s t T A N k, netTime_mem hst hT A N k⟩

/-- **The net argument in the form `RBM.Step1.NetLift` needs**: a `≺`-bound along every time
sequence for a *relaxed* family `(ξ', ζ')`, a high-probability event `Ξ` on which `ξ` at a time
`u` is dominated by `ξ'` at any nearby time up to an additive `N^{-(B+2)}` while `ζ'` at that
nearby time is at most `2 ζ`, and a polynomial lower bound `N^{-B} ≤ ζ`.

The conclusion is the full Definition 2.1 (i) statement, i.e. with the **uncountable** union
over `u ∈ [s_N, t_N]` inside the probability.

Why a *relaxed* family is allowed: the family of (5.8) carries the indicator
`1(‖G_u‖_max ≤ 2)`, which is not continuous in `u`, so `ξ` at `u` is *not* controlled by `ξ` at
a nearby net point — but it is controlled by the family with the threshold raised to `2 + o(1)`
(the "threshold `2 + o(1)` at the net points" of the paper's argument, see the deviations of
`RBM1D/Hierarchy/Step1.lean`).  Taking `ξ' = ξ`, `ζ' = ζ` gives the plain form. -/
theorem stochDom_of_forall_seq_relaxed {V : ℕ → Type*}
    {ξ ζ ξ' ζ' : ∀ N, RBM.TimeIcc s t N × V N → Ωb → ℝ} (hst : ∀ N, s N ≤ t N) {T : ℝ}
    (hT : 0 < T) (hlen : ∀ N, t N - s N ≤ T) {A B : ℝ} (hA : 0 ≤ A)
    (hrel : ∀ u : ∀ N, RBM.TimeIcc s t N,
      StochDom P (fun N v ω => ξ' N (u N, v) ω) (fun N v ω => ζ' N (u N, v) ω))
    {Ξ : ℕ → Set Ωb} (hΞ : HighProb P Ξ)
    (hlow : ∀ᶠ N : ℕ in atTop, ∀ (p : RBM.TimeIcc s t N × V N) (ω : Ωb),
      (N : ℝ) ^ (-B) ≤ ζ N p ω)
    (hclose : ∀ᶠ N : ℕ in atTop, ∀ ω ∈ Ξ N, ∀ u u' : RBM.TimeIcc s t N,
      |(u : ℝ) - (u' : ℝ)| ≤ (N : ℝ) ^ (-A) → ∀ v : V N,
        ξ N (u, v) ω ≤ ξ' N (u', v) ω + (N : ℝ) ^ (-(B + 2)) ∧
        ζ' N (u', v) ω ≤ 2 * ζ N (u, v) ω) :
    StochDom P ξ ζ := by
  have hA1 : (0 : ℝ) ≤ A + 1 := by linarith
  -- the net family: the relaxed family sampled at the `N^{-(A+1)}`-net of `[s_N, t_N]`
  have hnet := stochDom_reindex_of_forall_seq (V := V)
    (W := fun N => Fin (netSize (A + 1) N + 1)) hst hrel
    (fun N k => netTimeIcc (s := s) (t := t) hst hT.le (A + 1) N k)
    (C := A + 1 + 1) (by linarith) (card_net_le hA1)
  refine stochDom_of_subset_highProb hnet hΞ fun τ hτ => ⟨τ / 2, half_pos hτ, ?_⟩
  have hτ2 : 0 < τ / 2 := half_pos hτ
  filter_upwards [hclose, hlow, eventually_ge_atTop 2, eventually_le_rpow T one_pos,
    eventually_le_rpow 3 hτ2] with N hcloseN hlowN hN2 hTN hN3
  rintro ω ⟨⟨⟨u, v⟩, hbad⟩, hωΞ⟩
  have hNpos : (0 : ℝ) < N := by positivity
  have hN2' : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
  have hNpos' : (0 : ℝ) < (N : ℝ) := by linarith
  rw [Real.rpow_one] at hTN
  -- a net point within `N^{-A}` of `u`
  have hmpos : (0 : ℝ) < (netSize (A + 1) N : ℝ) := by exact_mod_cast netSize_pos (A + 1) N
  have hmge : (N : ℝ) ^ (A + 1) ≤ (netSize (A + 1) N : ℝ) := rpow_le_netSize _ _
  have hNA1 : (0 : ℝ) < (N : ℝ) ^ (A + 1) := Real.rpow_pos_of_pos hNpos' _
  obtain ⟨k, hk⟩ := exists_netTime_close (s := s) (t := t) hT hlen (A + 1) N u.2
  have hdist : |(u : ℝ) - ((netTimeIcc (s := s) (t := t) hst hT.le (A + 1) N k : ℝ))|
      ≤ (N : ℝ) ^ (-A) := by
    refine hk.trans ?_
    have h1 : T / (netSize (A + 1) N : ℝ) ≤ T / (N : ℝ) ^ (A + 1) := by
      gcongr
    refine h1.trans ?_
    rw [div_le_iff₀ hNA1]
    have hmul : (N : ℝ) ^ (-A) * (N : ℝ) ^ (A + 1) = (N : ℝ) ^ (1 : ℝ) := by
      rw [← Real.rpow_add hNpos']; ring_nf
    rw [hmul, Real.rpow_one]
    exact hTN
  obtain ⟨hξ, hζ⟩ := hcloseN ω hωΞ u _ hdist v
  -- the arithmetic
  set z : ℝ := ζ N (u, v) ω with hz_def
  set z' : ℝ := ζ' N (netTimeIcc (s := s) (t := t) hst hT.le (A + 1) N k, v) ω with hz'_def
  set x : ℝ := ξ N (u, v) ω with hx_def
  set x' : ℝ := ξ' N (netTimeIcc (s := s) (t := t) hst hT.le (A + 1) N k, v) ω with hx'_def
  have hzlow : (N : ℝ) ^ (-B) ≤ z := hlowN (u, v) ω
  have hz0 : (0 : ℝ) ≤ z := le_trans (Real.rpow_nonneg hNpos'.le _) hzlow
  have hBB : (N : ℝ) ^ (-(B + 2)) < (N : ℝ) ^ (-B) := by
    refine Real.rpow_lt_rpow_of_exponent_lt (by linarith) (by linarith)
  have hhalf : (N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (τ / 2) = (N : ℝ) ^ τ := by
    rw [← Real.rpow_add hNpos']; ring_nf
  have hbig : (1 : ℝ) ≤ (N : ℝ) ^ τ - 2 * (N : ℝ) ^ (τ / 2) := by
    nlinarith [hhalf, hN3]
  have hprod : (0 : ℝ) ≤ ((N : ℝ) ^ τ - 2 * (N : ℝ) ^ (τ / 2) - 1) * z :=
    mul_nonneg (by linarith) hz0
  have hhalf0 : (0 : ℝ) ≤ (N : ℝ) ^ (τ / 2) := Real.rpow_nonneg hNpos'.le _
  have hz'le : (N : ℝ) ^ (τ / 2) * z' ≤ (N : ℝ) ^ (τ / 2) * (2 * z) :=
    mul_le_mul_of_nonneg_left hζ hhalf0
  refine ⟨(k, v), ?_⟩
  show (N : ℝ) ^ (τ / 2) * z' < x'
  nlinarith [hbad, hξ, hprod, hzlow, hBB, hz'le]

/-- **`RBM.Step1.NetLift` from a modulus of continuity valid with high probability.**  The
family is its own relaxation (`ξ' = ξ`, `ζ' = ζ`), so the sequence hypothesis that `NetLift`
receives is the one that is used.  This is the plain "`N^{-C}` net + (5.1)" of p. 51. -/
theorem netLift_of_modulus_hp {V : ℕ → Type*}
    {ξ ζ : ∀ N, RBM.TimeIcc s t N × V N → Ωb → ℝ} (hst : ∀ N, s N ≤ t N) {T : ℝ} (hT : 0 < T)
    (hlen : ∀ N, t N - s N ≤ T) {A B : ℝ} (hA : 0 ≤ A) {Ξ : ℕ → Set Ωb} (hΞ : HighProb P Ξ)
    (hlow : ∀ᶠ N : ℕ in atTop, ∀ (p : RBM.TimeIcc s t N × V N) (ω : Ωb),
      (N : ℝ) ^ (-B) ≤ ζ N p ω)
    (hclose : ∀ᶠ N : ℕ in atTop, ∀ ω ∈ Ξ N, ∀ u u' : RBM.TimeIcc s t N,
      |(u : ℝ) - (u' : ℝ)| ≤ (N : ℝ) ^ (-A) → ∀ v : V N,
        ξ N (u, v) ω ≤ ξ N (u', v) ω + (N : ℝ) ^ (-(B + 2)) ∧
        ζ N (u', v) ω ≤ 2 * ζ N (u, v) ω) :
    Step1.NetLift P s t ξ ζ :=
  fun h => stochDom_of_forall_seq_relaxed hst hT hlen hA h hΞ hlow hclose

/-- **`RBM.Step1.NetLift` from a *relaxed* family.**  When the family itself has no modulus in
`u` — the case of (5.8), whose indicator `1(‖G_u‖_max ≤ 2)` jumps — the net argument still
closes provided the same `≺`-bound along time sequences is available for a relaxed family
`(ξ', ζ')` that dominates `(ξ, ζ)` at nearby times.  The `NetLift` hypothesis is then not used
at all: `lift` is reduced to the *relaxed* sequence bound. -/
theorem netLift_of_relaxed {V : ℕ → Type*}
    {ξ ζ ξ' ζ' : ∀ N, RBM.TimeIcc s t N × V N → Ωb → ℝ} (hst : ∀ N, s N ≤ t N) {T : ℝ}
    (hT : 0 < T) (hlen : ∀ N, t N - s N ≤ T) {A B : ℝ} (hA : 0 ≤ A)
    (hrel : ∀ u : ∀ N, RBM.TimeIcc s t N,
      StochDom P (fun N v ω => ξ' N (u N, v) ω) (fun N v ω => ζ' N (u N, v) ω))
    {Ξ : ℕ → Set Ωb} (hΞ : HighProb P Ξ)
    (hlow : ∀ᶠ N : ℕ in atTop, ∀ (p : RBM.TimeIcc s t N × V N) (ω : Ωb),
      (N : ℝ) ^ (-B) ≤ ζ N p ω)
    (hclose : ∀ᶠ N : ℕ in atTop, ∀ ω ∈ Ξ N, ∀ u u' : RBM.TimeIcc s t N,
      |(u : ℝ) - (u' : ℝ)| ≤ (N : ℝ) ^ (-A) → ∀ v : V N,
        ξ N (u, v) ω ≤ ξ' N (u', v) ω + (N : ℝ) ^ (-(B + 2)) ∧
        ζ' N (u', v) ω ≤ 2 * ζ N (u, v) ω) :
    Step1.NetLift P s t ξ ζ :=
  fun _ => stochDom_of_forall_seq_relaxed hst hT hlen hA hrel hΞ hlow hclose

end NetLift

/-! ### The assembly of `RBM.Step1.Hyp` for the Gaussian model -/

section Assembly

/-- **`RBM.Step1.Hyp` for the Gaussian model.**  Three of the four fields are theorems:
`scaling` is `RBM.Gauss.loopScaling_gauss` (T111), `lemma41` is `RBM.Gauss.lemma41Flow` (T108)
given the time-indexed (4.2)/(4.3), and `cont` is `RBM.Gauss.cont_gauss` (this file,
unconditional).  Only `lift` is still an input; see `stochDom_of_forall_seq_relaxed` for what
it reduces to. -/
theorem step1Hyp_gauss (d : Dims) {E : ℝ} (hE : |E| < 2) {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N)
    (ht1 : ∀ N, t N < 1) (hEntry : EntryBoundFlow d E s t) (hDiag : DiagBoundFlow d E s t)
    (hlift : ∀ n : ℕ, 1 ≤ n → Step1.NetLift (P d) s t
      (Step1.loopInd (sample d) E s t n) (Step1.aprioriRhs (band d) E s t n)) :
    Step1.Hyp (sample d) E s t where
  scaling := fun t₁ t₂ h1 h12 _ =>
    loopScaling_gauss (d := d) (fun N => lt_of_lt_of_le (by norm_num : (0:ℝ) < 1/2) (h1 N)) h12
  lift := hlift
  lemma41 := lemma41Flow hE hs0 ht1 hEntry hDiag
  cont := cont_gauss d hE (fun N => (hs0 N)) ht1

end Assembly

/-! ## T125: `lift` discharged

The four items that T116 left open are settled below, in the order of the list in
"What is not done".

* **(1)** the modulus in `u` of `‖L_{u,σ,a}‖`: `norm_gchain_sub_le` (a telescoping estimate for
  `RBM.gchain`, deterministic), `norm_gloop_sub_le`, and its Gaussian form
  `norm_Lval_sub_le_sqrt` — `|L_u - L_{u'}| ≤ n η_t^{-(n+1)}(‖X‖+1)|u-u'|^{1/2}`.
* **(2)** the slow variation `ζ(u') ≤ 2 ζ(u)`: `aprioriRhs_eq` shows that the right side of
  (5.8) is `(ℓ_s W η_u)^{-n+1}`, i.e. depends on `u` **only through `η_u`** (the two factors
  `ℓ_u` cancel), and `aprioriRhs_le_two_mul` is then Bernoulli's inequality — it needs the net
  spacing below `(1-t_N)/(2(n-1))`, the regime hypothesis.
* **(3)** the polynomial lower bound: `rpow_neg_le_aprioriRhs`, `N^{-(n-1)} ≤ ζ`, because
  `ℓ_s W η_u ≤ W L ≤ N`.
* **(4)** Lemma 5.1 at the threshold `2 + o(1)`: **this turned out to be a generalization that
  was already available**, not new mathematics.  The threshold `2` is a *proof constant* of
  §6, not a structural one, and `RBM.lemma_5_1_thr` / `RBM.lemma_5_1'_thr`
  (`RBM1D/Loop/ContinuityAssembly.lean`, added by T125) carry an arbitrary threshold `C₀ ≥ 0`
  through.  `eq58_seq_thr` is then `RBM.Step1.eq58_seq` at the threshold `C₀`.

`netLift_gauss` assembles the four into `RBM.Step1.NetLift` via T116's `netLift_of_relaxed`,
with the relaxed threshold `C₀ = 3` and net spacing `N^{-A}`,
`A = 2(c(n+1) + n + 3)`; `step1Hyp_gauss_of_regime` is the resulting complete `RBM.Step1.Hyp`.

The one hypothesis that looks new is the **regime** `∃ c > 0, t_N ≤ 1 - N^{-c}` (`hreg`),
which is the paper's own `t ≤ 1 - N^{-1+τ}`: without it the net spacing cannot be made small
compared with `1 - t_N`, and both the threshold shift and the slow variation fail.  It is not
actually new either: `rpow_neg_one_le_one_sub_of_scale_ge` derives it (with `c = 1`) from
`RBM.Step1.step1`'s own `N^c ≤ W ℓ_t η_t`, since `W ℓ_t ≤ W L ≤ N`.  Hence
`step1Hyp_gauss_of_scale` produces a complete `RBM.Step1.Hyp` under **exactly** the hypotheses
of `RBM.Step1.step1` plus (4.2)/(4.3) along the flow (T107, still without a producer).
-/

section ChainModulus

variable {L W : ℕ} [NeZero L] [NeZero W]
  {H H' : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ} {z z' : ℂ}

theorem norm_Eblk_le_one (b : ZMod L) : ‖Eblk L W b‖ ≤ 1 := by
  refine (norm_Eblk_le (W := W) b).trans ?_
  have hW : (1 : ℝ) ≤ W := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne W)
  rw [inv_le_one_iff₀]
  right; exact hW

/-- `‖C_{σ,a}‖ ≤ M^{|σ|}` when every `‖G(σ)‖ ≤ M`. -/
theorem norm_gchain_le_pow {M : ℝ} (hG : ∀ s, ‖Gsig H z s‖ ≤ M) :
    ∀ (σ : List Bool) (a : List (ZMod L)), σ.length = a.length + 1 →
      ‖gchain L W H z σ a‖ ≤ M ^ σ.length := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hG true)
  intro σ
  induction σ with
  | nil => intro a h; simp at h
  | cons s σ ih =>
    intro a h
    cases a with
    | nil =>
      have hσ : σ = [] := List.eq_nil_of_length_eq_zero (by simpa using h)
      subst hσ
      simpa using hG s
    | cons b a =>
      have h' : σ.length = a.length + 1 := by simpa using h
      rw [gchain_cons, List.length_cons, pow_succ']
      refine (norm_mul_le _ _).trans ?_
      refine (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)).trans ?_
      calc ‖Gsig H z s‖ * ‖Eblk L W b‖ * ‖gchain L W H z σ a‖
          ≤ M * 1 * M ^ σ.length :=
            mul_le_mul (mul_le_mul (hG s) (norm_Eblk_le_one b) (norm_nonneg _) hM0)
              (ih a h') (norm_nonneg _) (by positivity)
        _ = M * M ^ σ.length := by ring

/-- **The telescoping modulus for chains**: two chains with the same index `(σ, a)` but
different `(H, z)` differ by at most `|σ| δ M^{|σ|-1}`, where `M` bounds every `‖G(σ)‖` on
both sides and `δ` bounds every `‖G(σ) - G'(σ)‖`. -/
theorem norm_gchain_sub_le {M δ : ℝ} (hM : 1 ≤ M) (hG : ∀ s, ‖Gsig H z s‖ ≤ M)
    (hG' : ∀ s, ‖Gsig H' z' s‖ ≤ M) (hδ : ∀ s, ‖Gsig H z s - Gsig H' z' s‖ ≤ δ) :
    ∀ (σ : List Bool) (a : List (ZMod L)), σ.length = a.length + 1 →
      ‖gchain L W H z σ a - gchain L W H' z' σ a‖ ≤ σ.length * (δ * M ^ (σ.length - 1)) := by
  have hM0 : (0 : ℝ) ≤ M := by linarith
  have hδ0 : 0 ≤ δ := le_trans (norm_nonneg _) (hδ true)
  intro σ
  induction σ with
  | nil => intro a h; simp at h
  | cons s σ ih =>
    intro a h
    cases a with
    | nil =>
      have hσ : σ = [] := List.eq_nil_of_length_eq_zero (by simpa using h)
      subst hσ
      simpa using hδ s
    | cons b a =>
      have h' : σ.length = a.length + 1 := by simpa using h
      have hk : 1 ≤ σ.length := by omega
      have e : Gsig H z s * Eblk L W b * gchain L W H z σ a
          - Gsig H' z' s * Eblk L W b * gchain L W H' z' σ a
          = (Gsig H z s - Gsig H' z' s) * Eblk L W b * gchain L W H z σ a
            + Gsig H' z' s * Eblk L W b * (gchain L W H z σ a - gchain L W H' z' σ a) := by
        simp only [Matrix.sub_mul, Matrix.mul_sub]
        abel
      rw [gchain_cons, gchain_cons, e, List.length_cons]
      have h1 : ‖(Gsig H z s - Gsig H' z' s) * Eblk L W b * gchain L W H z σ a‖
          ≤ δ * 1 * M ^ σ.length := by
        refine (norm_mul_le _ _).trans ?_
        refine (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)).trans ?_
        exact mul_le_mul (mul_le_mul (hδ s) (norm_Eblk_le_one b) (norm_nonneg _) hδ0)
          (norm_gchain_le_pow hG σ a h') (norm_nonneg _) (by positivity)
      have h2 : ‖Gsig H' z' s * Eblk L W b * (gchain L W H z σ a - gchain L W H' z' σ a)‖
          ≤ M * 1 * (σ.length * (δ * M ^ (σ.length - 1))) := by
        refine (norm_mul_le _ _).trans ?_
        refine (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)).trans ?_
        exact mul_le_mul (mul_le_mul (hG' s) (norm_Eblk_le_one b) (norm_nonneg _) hM0)
          (ih a h') (norm_nonneg _) (by positivity)
      have hpow : M * M ^ (σ.length - 1) = M ^ σ.length := by
        rw [← pow_succ']
        congr 1
        omega
      calc ‖(Gsig H z s - Gsig H' z' s) * Eblk L W b * gchain L W H z σ a
            + Gsig H' z' s * Eblk L W b * (gchain L W H z σ a - gchain L W H' z' σ a)‖
          ≤ δ * 1 * M ^ σ.length + M * 1 * (σ.length * (δ * M ^ (σ.length - 1))) :=
            (norm_add_le _ _).trans (add_le_add h1 h2)
        _ = ((σ.length : ℝ) + 1) * (δ * M ^ σ.length) := by
            rw [show M * 1 * ((σ.length : ℝ) * (δ * M ^ (σ.length - 1)))
              = (σ.length : ℝ) * (δ * (M * M ^ (σ.length - 1))) by ring, hpow]
            ring
        _ = ((σ.length + 1 : ℕ) : ℝ) * (δ * M ^ (σ.length + 1 - 1)) := by
            rw [Nat.add_sub_cancel]; push_cast; ring

/-- **The telescoping modulus for loops**: `|L_{σ,a}(H,z) - L_{σ,a}(H',z')| ≤ n δ M^{n-1}`. -/
theorem norm_gloop_sub_le {M δ : ℝ} (hM : 1 ≤ M) (hG : ∀ s, ‖Gsig H z s‖ ≤ M)
    (hG' : ∀ s, ‖Gsig H' z' s‖ ≤ M) (hδ : ∀ s, ‖Gsig H z s - Gsig H' z' s‖ ≤ δ)
    (I : LoopIdx (ZMod L)) (hwf : I.σ.length = I.a.length) (hn : 1 ≤ I.a.length) :
    ‖gloop L W H z I - gloop L W H' z' I‖
      ≤ I.a.length * (δ * M ^ (I.a.length - 1)) := by
  obtain ⟨σ, a⟩ := I
  simp only at hwf hn ⊢
  rcases List.eq_nil_or_concat' a with rfl | ⟨a', b, rfl⟩
  · simp at hn
  have h : σ.length = a'.length + 1 := by simpa using hwf
  rw [← trace_gchain_mul_Eblk h b, ← trace_gchain_mul_Eblk h b, ← Matrix.trace_sub,
    ← Matrix.sub_mul]
  refine (norm_trace_mul_Eblk_le _ b).trans ?_
  refine (norm_gchain_sub_le hM hG hG' hδ σ a' h).trans (le_of_eq ?_)
  rw [h]
  simp

end ChainModulus

section GaussLoopModulus

open Matrix

/-- The two charges give the same difference: `G(-) = G(+)ᴴ` for Hermitian `H`. -/
theorem norm_Gsig_sub_le_green_sub {n : Type*} [Fintype n] [DecidableEq n]
    {H H' : Matrix n n ℂ} (hH : H.IsHermitian) (hH' : H'.IsHermitian) (z z' : ℂ) (σ : Bool) :
    ‖Gsig H z σ - Gsig H' z' σ‖ ≤ ‖green H z - green H' z'‖ := by
  cases σ
  · have h1 : Gsig H z false = (green H z)ᴴ := by
      have h := Gsig_conjTranspose hH z true
      simp only [Bool.not_true, Gsig_true] at h
      exact h.symm
    have h2 : Gsig H' z' false = (green H' z')ᴴ := by
      have h := Gsig_conjTranspose hH' z' true
      simp only [Bool.not_true, Gsig_true] at h
      exact h.symm
    rw [h1, h2, ← Matrix.conjTranspose_sub, l2_opNorm_conjTranspose]
  · simp only [Gsig_true]
    exact le_rfl

/-- `1 ≤ η_t⁻¹` for `0 ≤ t < 1` (from `RBM.etaT_le_one`). -/
theorem one_le_inv_etaT {E : ℝ} (hE : |E| < 2) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    1 ≤ (etaT E t)⁻¹ := by
  have h := RBM.etaT_le_one hE ht0
  have hpos := etaT_pos_of_lt_one' hE ht1
  rw [le_inv_comm₀ one_pos hpos]
  simpa using h

/-- `‖G_u(σ)‖ ≤ η_t⁻¹` on `[s, t]`, both charges. -/
theorem norm_Gsig_flow_le (d : Dims) (N : ℕ) {E : ℝ} (hE : |E| < 2) {t : ℝ} (ht1 : t < 1)
    (ω : Ω d) {u : ℝ} (hut : u ≤ t) (σ : Bool) :
    ‖Gsig (Hflow d N u ω) (zt E u) σ‖ ≤ (etaT E t)⁻¹ := by
  have hu1 : u < 1 := lt_of_le_of_lt hut ht1
  have hηu : 0 < etaT E u := etaT_pos_of_lt_one' hE hu1
  have hηt : 0 < etaT E t := etaT_pos_of_lt_one' hE ht1
  have hzim : (zt E u).im ≠ 0 := by rw [← etaT_eq_zt_im]; exact hηu.ne'
  have habs : |(zt E u).im| = etaT E u := by rw [← etaT_eq_zt_im, abs_of_pos hηu]
  refine (norm_Gsig_le (Hflow_isHermitian d N u ω) hzim σ).trans ?_
  rw [habs]
  exact inv_anti₀ hηt (etaT_le_of_le hE hut)

/-- The `√`-modulus of `G_u(σ)` on `[s, t]`, both charges. -/
theorem norm_Gsig_flow_sub_le_sqrt (d : Dims) (N : ℕ) {E : ℝ} (hE : |E| < 2) {s t : ℝ}
    (hs0 : 0 ≤ s) (ht1 : t < 1) (ω : Ω d) {u u' : ℝ} (hu : u ∈ Set.Icc s t)
    (hu' : u' ∈ Set.Icc s t) (σ : Bool) :
    ‖Gsig (Hflow d N u ω) (zt E u) σ - Gsig (Hflow d N u' ω) (zt E u') σ‖
      ≤ ((etaT E t)⁻¹ * (etaT E t)⁻¹ * (‖Xmat d N ω‖ + 1)) * Real.sqrt |u - u'| :=
  (norm_Gsig_sub_le_green_sub (Hflow_isHermitian d N u ω) (Hflow_isHermitian d N u' ω)
    (zt E u) (zt E u') σ).trans (norm_green_flow_sub_le_sqrt d N hE hs0 ht1 ω hu hu')

/-- **Item (1): the modulus in `u` of the loop values `L_{u,σ,a}`.**  A telescoping estimate
for `RBM.gloop`: with `n` resolvents, each of norm `≤ η_t^{-1}`, and each moving by at most
`η_t^{-2}(‖X‖+1)|u-u'|^{1/2}`, the loop moves by at most `n` times that, times `η_t^{-(n-1)}`. -/
theorem norm_Lval_sub_le_sqrt (d : Dims) (N : ℕ) {E : ℝ} (hE : |E| < 2) {s t : ℝ}
    (hs0 : 0 ≤ s) (ht1 : t < 1) (ω : Ω d) {u u' : ℝ} (hu : u ∈ Set.Icc s t)
    (hu' : u' ∈ Set.Icc s t) {n : ℕ} (hn : 1 ≤ n) (v : LoopData ((band d).L N) n) :
    ‖(sample d).Lval E N u ω v.idx - (sample d).Lval E N u' ω v.idx‖
      ≤ (n : ℝ) * (((etaT E t)⁻¹ * (etaT E t)⁻¹ * (‖Xmat d N ω‖ + 1)) * Real.sqrt |u - u'|
          * (etaT E t)⁻¹ ^ (n - 1)) := by
  have ht0 : (0 : ℝ) ≤ t := le_trans hs0 (le_trans hu.1 hu.2)
  have hM : (1 : ℝ) ≤ (etaT E t)⁻¹ := one_le_inv_etaT hE ht0 ht1
  have hlen : v.idx.a.length = n := by simp [LoopData.idx]
  have h := norm_gloop_sub_le (L := (band d).L N) (W := (band d).W N)
    (H := Hflow d N u ω) (H' := Hflow d N u' ω) (z := zt E u) (z' := zt E u') hM
    (fun σ => norm_Gsig_flow_le d N hE ht1 ω hu.2 σ)
    (fun σ => norm_Gsig_flow_le d N hE ht1 ω hu'.2 σ)
    (fun σ => norm_Gsig_flow_sub_le_sqrt d N hE hs0 ht1 ω hu hu' σ)
    v.idx (by simp [LoopData.idx]) (by simp [LoopData.idx]; omega)
  rw [hlen] at h
  exact h

end GaussLoopModulus


section AprioriArith

open Filter

/-- `κ N^α ≤ N^β` eventually in `N`, for `α < β`. -/
theorem eventually_const_mul_rpow_le_rpow (κ : ℝ) {α β : ℝ} (hαβ : α < β) :
    ∀ᶠ N : ℕ in atTop, κ * (N : ℝ) ^ α ≤ (N : ℝ) ^ β := by
  filter_upwards [eventually_le_rpow κ (by linarith : (0 : ℝ) < β - α), eventually_ge_atTop 1]
    with N hκ hN1
  have hN : (0 : ℝ) < N := by exact_mod_cast hN1
  calc κ * (N : ℝ) ^ α ≤ (N : ℝ) ^ (β - α) * (N : ℝ) ^ α :=
        mul_le_mul_of_nonneg_right hκ (Real.rpow_nonneg hN.le _)
    _ = (N : ℝ) ^ β := by rw [← Real.rpow_add hN]; congr 1; ring

variable {Ωb : Type*} [MeasurableSpace Ωb] {B : Band Ωb}

/-- **`(ℓ_u/ℓ_s)^{n-1}(Wℓ_uη_u)^{-n+1} = (ℓ_s W η_u)^{-n+1}`.**  The right side of (2.73)/(5.8)
depends on the time `u` **only through `η_u`**: the two factors of `ℓ_u` cancel. -/
theorem aprioriRhs_eq (E : ℝ) (s t : ℕ → ℝ) (n N : ℕ)
    (p : RBM.TimeIcc s t N × LoopData (B.L N) n) (ω : Ωb)
    (hℓu : 0 < B.ell N (p.1 : ℝ)) (hℓs : 0 < B.ell N (s N)) (hW : 0 < (B.W N : ℝ))
    (hη : 0 < etaT E (p.1 : ℝ)) :
    Step1.aprioriRhs B E s t n N p ω
      = (B.ell N (s N) * (B.W N : ℝ) * etaT E (p.1 : ℝ))⁻¹ ^ (n - 1) := by
  have h1 : B.ell N (p.1 : ℝ) ≠ 0 := hℓu.ne'
  have h2 : B.ell N (s N) ≠ 0 := hℓs.ne'
  have h3 : (B.W N : ℝ) ≠ 0 := hW.ne'
  have h4 : etaT E (p.1 : ℝ) ≠ 0 := hη.ne'
  rw [Step1.aprioriRhs, ← mul_pow]
  congr 1
  rw [Band.scale]
  field_simp

end AprioriArith


section AprioriBounds

open Filter

variable {Ωb : Type*} [MeasurableSpace Ωb] {B : Band Ωb}

/-- **Item (3): the polynomial lower bound `N^{-(n-1)} ≤ ζ`** for the right side of (5.8).
By `RBM.Gauss.aprioriRhs_eq` the right side is `(ℓ_s W η_u)^{-n+1}`, and `ℓ_s W η_u ≤ W L ≤ N`
because `ℓ_s ≤ L` and `η_u ≤ 1`. -/
theorem rpow_neg_le_aprioriRhs (B : Band Ωb) {E : ℝ} (hE : |E| < 2) {s t : ℕ → ℝ}
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {n : ℕ} (hn : 1 ≤ n) :
    ∀ᶠ N : ℕ in atTop, ∀ (p : RBM.TimeIcc s t N × LoopData (B.L N) n) (ω : Ωb),
      (N : ℝ) ^ (-((n : ℝ) - 1)) ≤ Step1.aprioriRhs B E s t n N p ω := by
  filter_upwards [B.dim, eventually_ge_atTop 1] with N hdim hN1
  intro p ω
  have hsu : s N ≤ (p.1 : ℝ) := p.1.2.1
  have hut : (p.1 : ℝ) ≤ t N := p.1.2.2
  have hu0 : (0 : ℝ) ≤ (p.1 : ℝ) := (hs0 N).trans hsu
  have hu1 : (p.1 : ℝ) < 1 := hut.trans_lt (ht1 N)
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  have hW : (0 : ℝ) < B.W N := by exact_mod_cast B.W_pos N
  have hL1 : 1 ≤ B.L N := B.one_le_L N
  have hℓu : 0 < B.ell N (p.1 : ℝ) := Step3.ellHat_pos_of_lt_one hL1 hu1
  have hℓs : 0 < B.ell N (s N) := Step3.ellHat_pos_of_lt_one hL1 hs1
  have hη : 0 < etaT E (p.1 : ℝ) := etaT_pos_of_lt_one' hE hu1
  rw [aprioriRhs_eq E s t n N p ω hℓu hℓs hW hη]
  set Q : ℝ := B.ell N (s N) * (B.W N : ℝ) * etaT E (p.1 : ℝ) with hQdef
  have hQ0 : 0 < Q := by rw [hQdef]; positivity
  have hQN : Q ≤ (N : ℝ) := by
    have h1 : B.ell N (s N) ≤ (B.L N : ℝ) := min_le_right _ _
    have h2 : etaT E (p.1 : ℝ) ≤ 1 := RBM.etaT_le_one hE hu0
    have hWL : (B.W N : ℝ) * B.L N ≤ N := by exact_mod_cast hdim.1
    calc Q ≤ (B.L N : ℝ) * (B.W N : ℝ) * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_right h1 hW.le) h2 hη.le (by positivity)
      _ = (B.W N : ℝ) * B.L N := by ring
      _ ≤ (N : ℝ) := hWL
  have hcast : -((n : ℝ) - 1) = -(((n - 1 : ℕ) : ℝ)) := by
    have : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      have : (1 : ℕ) ≤ n := hn
      push_cast [Nat.cast_sub this]
      ring
    rw [this]
  rw [hcast, Real.rpow_neg (Nat.cast_nonneg N), Real.rpow_natCast, inv_pow]
  exact inv_anti₀ (pow_pos hQ0 _) (pow_le_pow_left₀ hQ0.le hQN _)

/-- `x^k ≤ 2 y^k` transfers to the inverses: `(Ry)^{-k} ≤ 2 (Rx)^{-k}`. -/
theorem inv_pow_le_two_mul_inv_pow {R x y : ℝ} {k : ℕ} (hR : 0 < R) (hx : 0 < x) (hy : 0 < y)
    (h : x ^ k ≤ 2 * y ^ k) : ((R * y)⁻¹) ^ k ≤ 2 * ((R * x)⁻¹) ^ k := by
  have hRk : (0 : ℝ) < R ^ k := pow_pos hR k
  have hkey : (R * x) ^ k ≤ 2 * (R * y) ^ k := by
    rw [mul_pow, mul_pow]
    calc R ^ k * x ^ k ≤ R ^ k * (2 * y ^ k) := mul_le_mul_of_nonneg_left h hRk.le
      _ = 2 * (R ^ k * y ^ k) := by ring
  have hA : (0 : ℝ) < (R * y) ^ k := pow_pos (mul_pos hR hy) k
  have hB : (0 : ℝ) < (R * x) ^ k := pow_pos (mul_pos hR hx) k
  rw [inv_pow, inv_pow, ← one_div, ← one_div, mul_one_div, div_le_div_iff₀ hA hB, one_mul]
  exact hkey

/-- The elementary inequality behind the slow variation of `ζ`: if `|u - u'| ≤ ε` and
`2 k ε ≤ 1 - T` with `u, u' ≤ T < 1`, then `(1-u)^k ≤ 2 (1-u')^k`.  (Bernoulli:
`(1 - 1/(2k))^k ≥ 1/2`.) -/
theorem pow_one_sub_le_two_mul {k : ℕ} {u u' T ε : ℝ} (hk : 1 ≤ k) (huT : u ≤ T) (hu'T : u' ≤ T)
    (hT : T < 1) (hcl : |u - u'| ≤ ε) (hsmall : 2 * (k : ℝ) * ε ≤ 1 - T) :
    (1 - u) ^ k ≤ 2 * (1 - u') ^ k := by
  have hk0 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hx : 0 < 1 - u := by linarith
  have hx' : 0 < 1 - u' := by linarith
  have hεx : 2 * (k : ℝ) * ε ≤ 1 - u := by linarith
  set a : ℝ := -(1 / (2 * (k : ℝ))) with ha
  have h2k : (0 : ℝ) < 2 * (k : ℝ) := by linarith
  have hainv : (1 : ℝ) / (2 * (k : ℝ)) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ h2k (by norm_num : (0:ℝ) < 2)]; linarith
  have ha2 : (-2 : ℝ) ≤ a := by rw [ha]; linarith [div_nonneg (zero_le_one (α := ℝ)) h2k.le]
  have hka : (k : ℝ) * a = -(1 / 2) := by
    rw [ha]
    field_simp
  have hber : (1 : ℝ) / 2 ≤ (1 + a) ^ k := by
    have h := one_add_mul_le_pow ha2 k
    rw [hka] at h
    linarith
  have h1a : (0 : ℝ) ≤ 1 + a := by rw [ha]; linarith
  have hle : (1 - u) * (1 + a) ≤ 1 - u' := by
    have hd : u' - u ≤ ε := by
      have := abs_le.1 hcl
      linarith [this.1]
    have hεk : ε ≤ (1 - u) / (2 * (k : ℝ)) := by
      rw [le_div_iff₀ h2k]; linarith
    have hexp : (1 - u) * (1 + a) = (1 - u) - (1 - u) / (2 * (k : ℝ)) := by
      rw [ha]; field_simp; ring
    rw [hexp]
    linarith
  calc (1 - u) ^ k = 2 * ((1 - u) ^ k * (1 / 2)) := by ring
    _ ≤ 2 * ((1 - u) ^ k * (1 + a) ^ k) := by
        have : (1 - u) ^ k * (1 / 2) ≤ (1 - u) ^ k * (1 + a) ^ k :=
          mul_le_mul_of_nonneg_left hber (pow_nonneg hx.le _)
        linarith
    _ = 2 * ((1 - u) * (1 + a)) ^ k := by rw [mul_pow]
    _ ≤ 2 * (1 - u') ^ k := by
        have := pow_le_pow_left₀ (mul_nonneg hx.le h1a) hle k
        linarith

/-- **Item (2): the slow variation `ζ(u') ≤ 2 ζ(u)`** of the right side of (5.8), for net
spacing `ε` below `(1 - t_N)/(2(n-1))`. -/
theorem aprioriRhs_le_two_mul (B : Band Ωb) {E : ℝ} (hE : |E| < 2) {s t : ℕ → ℝ}
    (_hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {n : ℕ} (_hn : 1 ≤ n)
    {N : ℕ} {ε : ℝ} (hsmall : 2 * ((n - 1 : ℕ) : ℝ) * ε ≤ 1 - t N)
    (u u' : RBM.TimeIcc s t N) (hcl : |(u : ℝ) - (u' : ℝ)| ≤ ε) (v : LoopData (B.L N) n)
    (ω : Ωb) :
    Step1.aprioriRhs B E s t n N (u', v) ω ≤ 2 * Step1.aprioriRhs B E s t n N (u, v) ω := by
  have hW : (0 : ℝ) < B.W N := by exact_mod_cast B.W_pos N
  have hL1 : 1 ≤ B.L N := B.one_le_L N
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  have hℓs : 0 < B.ell N (s N) := Step3.ellHat_pos_of_lt_one hL1 hs1
  have hu1 : (u : ℝ) < 1 := u.2.2.trans_lt (ht1 N)
  have hu'1 : (u' : ℝ) < 1 := u'.2.2.trans_lt (ht1 N)
  have hℓu : 0 < B.ell N (u : ℝ) := Step3.ellHat_pos_of_lt_one hL1 hu1
  have hℓu' : 0 < B.ell N (u' : ℝ) := Step3.ellHat_pos_of_lt_one hL1 hu'1
  have hηu : 0 < etaT E (u : ℝ) := etaT_pos_of_lt_one' hE hu1
  have hηu' : 0 < etaT E (u' : ℝ) := etaT_pos_of_lt_one' hE hu'1
  rw [aprioriRhs_eq E s t n N (u', v) ω hℓu' hℓs hW hηu',
    aprioriRhs_eq E s t n N (u, v) ω hℓu hℓs hW hηu]
  set k := n - 1 with hk
  rcases Nat.eq_zero_or_pos k with hk0 | hk1
  · rw [hk0]; norm_num
  set m0 : ℝ := (mE E).im with hm0
  have hm00 : 0 < m0 := mE_im_pos hE
  set R : ℝ := B.ell N (s N) * (B.W N : ℝ) * m0 with hR
  have hR0 : 0 < R := by rw [hR]; positivity
  have hQ : B.ell N (s N) * (B.W N : ℝ) * etaT E (u : ℝ) = R * (1 - (u : ℝ)) := by
    rw [hR]; show _ = _; unfold etaT; ring
  have hQ' : B.ell N (s N) * (B.W N : ℝ) * etaT E (u' : ℝ) = R * (1 - (u' : ℝ)) := by
    rw [hR]; show _ = _; unfold etaT; ring
  have hx : 0 < 1 - (u : ℝ) := by linarith
  have hx' : 0 < 1 - (u' : ℝ) := by linarith
  have hbase := pow_one_sub_le_two_mul (k := k) (T := t N) hk1 u.2.2 u'.2.2 (ht1 N) hcl
    (by exact_mod_cast hsmall)
  rw [hQ, hQ']
  exact inv_pow_le_two_mul_inv_pow hR0 hx hx' hbase

end AprioriBounds


section RelaxedEq58

open Filter MeasureTheory

variable {Ωb : Type*} [MeasurableSpace Ωb] {B : Band Ωb}

/-- The event `{‖G_u‖_max ≤ C₀}` at a single time `u` (`RBM.Step1.gEv` is `C₀ = 2`). -/
def gEvThr (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (C₀ : ℝ) : Set Ωb :=
  {ω | ∀ i j, ‖X.G E N u ω i j‖ ≤ C₀}

theorem gmaxEventThr_eq (X : Sample B) (E : ℝ) (τ : ℕ → ℝ) (C₀ : ℝ) (N : ℕ) :
    X.gmaxEventThr E τ C₀ N = gEvThr X E N (τ N) C₀ := rfl

theorem gEv_subset_gEvThr (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) {C₀ : ℝ} (hC₀ : 2 ≤ C₀) :
    Step1.gEv X E N u ⊆ gEvThr X E N u C₀ := fun _ hω i j => (hω i j).trans hC₀

/-- **The left side of (5.8) with the threshold raised to `C₀`**: `1(‖G_u‖_max ≤ C₀)|L_{u,σ,a}|`.
`C₀ = 2` is `RBM.Step1.loopInd`. -/
noncomputable def loopIndThr (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) (C₀ : ℝ) (n : ℕ) :
    ∀ N, RBM.TimeIcc s t N × LoopData (B.L N) n → Ωb → ℝ :=
  fun N p ω => (gEvThr X E N (p.1 : ℝ) C₀).indicator (fun ω => ‖X.Lval E N (p.1 : ℝ) ω p.2.idx‖) ω

theorem loopIndThr_nonneg (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) (C₀ : ℝ) (n N : ℕ)
    (p : RBM.TimeIcc s t N × LoopData (B.L N) n) (ω : Ωb) :
    0 ≤ loopIndThr X E s t C₀ n N p ω :=
  Set.indicator_nonneg (fun _ _ => norm_nonneg _) ω

/-- **Item (4): (5.8) along a time sequence with the raised threshold `C₀`.**  Verbatim the
proof of `RBM.Step1.eq58_seq`, with `RBM.lemma_5_1'` replaced by `RBM.lemma_5_1'_thr`. -/
theorem eq58_seq_thr (X : Sample B) {E : ℝ} {s t : ℕ → ℝ} {κ C₀ : ℝ} (hκ : 0 < κ)
    (hE : |E| ≤ 2 - κ) (hC₀ : 0 ≤ C₀) (hB : BoundsCore X E s) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hc : Cond272 B E s t)
    (hS : ∀ t₁ t₂ : ℕ → ℝ, (∀ N, 1 / 2 ≤ t₁ N) → (∀ N, t₁ N ≤ t₂ N) → (∀ N, t₂ N < 1) →
      LoopScaling X E t₁ t₂)
    (u : ∀ N, RBM.TimeIcc s t N) {n : ℕ} (hn : 1 ≤ n) :
    StochDom B.P (fun N (v : LoopData (B.L N) n) ω => loopIndThr X E s t C₀ n N (u N, v) ω)
      (fun N (v : LoopData (B.L N) n) ω => Step1.aprioriRhs B E s t n N (u N, v) ω) := by
  have hE2 : |E| < 2 := by linarith
  have h1 : ∀ N, 1 / 2 ≤ Step1.startTime s N := fun N => le_max_right _ _
  have h12 : ∀ N, Step1.startTime s N ≤ max (u N : ℝ) (Step1.startTime s N) := fun N =>
    le_max_right _ _
  have h2 : ∀ N, max (u N : ℝ) (Step1.startTime s N) < 1 := fun N =>
    max_lt ((u N).2.2.trans_lt (ht1 N)) (max_lt ((hst N).trans_lt (ht1 N)) (by norm_num))
  have h51 := lemma_5_1'_thr X hκ hE (c := 1 / 2) (by norm_num) hC₀ h1 h12 h2
    (hS _ _ h1 h12 h2) (Step1.eq55 X hκ hE hB hs0 hst ht1 hc) n hn
  set C : ℝ := (2 / (mE E).im) ^ n with hC
  have hm := mE_im_pos hE2
  have hC0 : 0 ≤ C := by positivity
  have hu0 : ∀ N, (0 : ℝ) ≤ (u N : ℝ) := fun N => (hs0 N).trans (u N).2.1
  have hu1 : ∀ N, (u N : ℝ) < 1 := fun N => (u N).2.2.trans_lt (ht1 N)
  have hζ0 : ∀ N, 0 ≤ (B.ell N (u N) / B.ell N (s N)) ^ (n - 1) *
      (B.scale E N (u N))⁻¹ ^ (n - 1) := fun N => by
    have h := Step1.one_le_ell_div (B := B) (N := N) (u N).2.1 (hu1 N)
    have := (B.scale_pos' hE2 N (hu0 N) (hu1 N))
    positivity
  have hdet : StochDom B.P
      (fun N (_ : LoopData (B.L N) n) (_ : Ωb) => C * ((B.ell N (u N) / B.ell N (s N)) ^ (n - 1) *
        (B.scale E N (u N))⁻¹ ^ (n - 1)))
      (fun N _ _ => (B.ell N (u N) / B.ell N (s N)) ^ (n - 1) *
        (B.scale E N (u N))⁻¹ ^ (n - 1)) :=
    Step1.stochDom_of_le_const_mul (fun N _ _ => mul_nonneg hC0 (hζ0 N)) (fun N _ _ => hζ0 N) C
      fun _ _ _ => le_rfl
  refine Step1.stochDom_of_forall_or h51 hdet fun N v ω => ?_
  by_cases h : Step1.startTime s N ≤ u N
  · left
    have ht2 : max (u N : ℝ) (Step1.startTime s N) = u N := max_eq_left h
    refine ⟨by simp only [loopIndThr, gmaxEventThr_eq, ht2, le_refl], ?_⟩
    simp only [Step1.aprioriRhs, ht2]
    have hL : 1 ≤ B.L N := B.one_le_L N
    have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
    have hℓs := Step3.ellHat_pos_of_lt_one (L := B.L N) hL hs1
    have hℓu := Step3.ellHat_pos_of_lt_one (L := B.L N) hL (hu1 N)
    have hmono : ellHat (B.L N) ((s N : ℝ) : ℂ) ≤ ellHat (B.L N) ((Step1.startTime s N : ℝ) : ℂ) :=
      Step3.ellHat_mono (le_max_left _ _) (h.trans_lt (hu1 N))
    have hA := (B.scale_pos' hE2 N (hu0 N) (hu1 N))
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    refine pow_le_pow_left₀ (div_nonneg hℓu.le (hℓs.trans_le hmono).le) ?_ _
    simp only [Band.ell]
    exact div_le_div_of_nonneg_left hℓu.le hℓs hmono
  · right
    push Not at h
    have hhalf : (u N : ℝ) ≤ 1 / 2 := by
      rcases lt_max_iff.1 h with h' | h'
      · exact absurd (u N).2.1 (not_le.2 h')
      · exact h'.le
    refine ⟨?_, le_rfl⟩
    have hind : loopIndThr X E s t C₀ n N (u N, v) ω ≤ ‖X.Lval E N (u N) ω v.idx‖ :=
      Set.indicator_le_self' (fun _ _ => norm_nonneg _) ω
    refine hind.trans ((Step1.norm_Lval_le_of_le_half X hE2 N (hu0 N) hhalf ω hn v).trans ?_)
    rw [← hC]
    have hR := one_le_pow₀ (n := n - 1) (Step1.one_le_ell_div (B := B) (N := N) (u N).2.1 (hu1 N))
    have hA := (B.scale_pos' hE2 N (hu0 N) (hu1 N))
    have hA' : 0 ≤ (B.scale E N (u N))⁻¹ ^ (n - 1) := by positivity
    have := mul_le_mul_of_nonneg_right hR hA'
    rw [one_mul] at this
    exact mul_le_mul_of_nonneg_left this hC0

end RelaxedEq58


section MasterSmall

open Filter

/-- **The master smallness estimate behind the net argument.**  With net spacing `N^{-A}` and
`η_t ≥ N^{-c} m_0` (the regime `t_N ≤ 1 - N^{-c}`), the quantity that controls both the shift
of the threshold and the shift of the loop values is below `N^{-(n+1)}`. -/
theorem eventually_master_small {n : ℕ} {c m0 A : ℝ} (hm0 : 0 < m0)
    (hA2 : A / 2 = c * ((n : ℝ) + 1) + (n : ℝ) + 3) :
    ∀ᶠ N : ℕ in atTop, ∀ η : ℝ, 0 < η → (N : ℝ) ^ (-c) * m0 ≤ η →
      (n : ℝ) * (η⁻¹) ^ (n + 1) * ((N : ℝ) + 1) * (N : ℝ) ^ (-(A / 2))
        ≤ (N : ℝ) ^ (-((n : ℝ) + 1)) := by
  have hαβ : c * ((n : ℝ) + 1) + 1 - A / 2 < -((n : ℝ) + 1) := by rw [hA2]; linarith
  filter_upwards [eventually_const_mul_rpow_le_rpow (2 * (n : ℝ) * (m0⁻¹) ^ (n + 1)) hαβ,
    eventually_ge_atTop 1] with N hκ hN1
  intro η hη hηlow
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNc : (0 : ℝ) < (N : ℝ) ^ (-c) := Real.rpow_pos_of_pos hN0 _
  have hinv : η⁻¹ ≤ (N : ℝ) ^ c * m0⁻¹ := by
    refine (inv_anti₀ (mul_pos hNc hm0) hηlow).trans (le_of_eq ?_)
    rw [mul_inv, Real.rpow_neg hN0.le, inv_inv]
  have hpow : (η⁻¹) ^ (n + 1) ≤ ((N : ℝ) ^ c * m0⁻¹) ^ (n + 1) :=
    pow_le_pow_left₀ (by positivity) hinv _
  have hcast : ((N : ℝ) ^ c) ^ (n + 1) = (N : ℝ) ^ (c * ((n : ℝ) + 1)) := by
    rw [← Real.rpow_natCast ((N : ℝ) ^ c) (n + 1), ← Real.rpow_mul hN0.le]
    congr 1
    push_cast
    ring
  have step1 : (n : ℝ) * (η⁻¹) ^ (n + 1) ≤ (n : ℝ) * ((N : ℝ) ^ c * m0⁻¹) ^ (n + 1) :=
    mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg n)
  have step2 : ((N : ℝ) + 1) ≤ 2 * (N : ℝ) := by linarith
  have hrest : (0 : ℝ) ≤ (N : ℝ) ^ (-(A / 2)) := Real.rpow_nonneg hN0.le _
  have heq : (n : ℝ) * ((N : ℝ) ^ c * m0⁻¹) ^ (n + 1) * (2 * (N : ℝ)) * (N : ℝ) ^ (-(A / 2))
      = (2 * (n : ℝ) * (m0⁻¹) ^ (n + 1)) * (N : ℝ) ^ (c * ((n : ℝ) + 1) + 1 - A / 2) := by
    rw [mul_pow, hcast,
      show c * ((n : ℝ) + 1) + 1 - A / 2 = c * ((n : ℝ) + 1) + (1 + -(A / 2)) by ring,
      Real.rpow_add hN0, Real.rpow_add hN0, Real.rpow_one]
    ring
  calc (n : ℝ) * (η⁻¹) ^ (n + 1) * ((N : ℝ) + 1) * (N : ℝ) ^ (-(A / 2))
      ≤ (n : ℝ) * ((N : ℝ) ^ c * m0⁻¹) ^ (n + 1) * (2 * (N : ℝ)) * (N : ℝ) ^ (-(A / 2)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul step1 step2 (by positivity) (by positivity)) hrest
    _ = (2 * (n : ℝ) * (m0⁻¹) ^ (n + 1)) * (N : ℝ) ^ (c * ((n : ℝ) + 1) + 1 - A / 2) := heq
    _ ≤ (N : ℝ) ^ (-((n : ℝ) + 1)) := hκ

end MasterSmall


section NetLiftGauss

open Filter MeasureTheory

/-- **`RBM.Step1.NetLift` for the Gaussian model, from the relaxed sequence bound.**  Items
(1)–(3) of the T116 list are discharged here; (4) is the hypothesis `hrel`, supplied by
`RBM.Gauss.eq58_seq_thr` (Lemma 5.1 at the threshold `3`).

The regime hypothesis `hreg` (`t_N ≤ 1 - N^{-c}`) is what makes the net spacing `N^{-A}`
smaller than a multiple of `1 - t_N`; it is the paper's own regime `t ≤ 1 - N^{-1+τ}`. -/
theorem netLift_gauss (d : Dims) {E : ℝ} (hE : |E| < 2) {s t : ℕ → ℝ}
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    {c : ℝ} (hc : 0 < c) (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-c) ≤ 1 - t N)
    {n : ℕ} (hn : 1 ≤ n)
    (hrel : ∀ u : ∀ N, RBM.TimeIcc s t N,
      StochDom (P d) (fun N v ω => loopIndThr (sample d) E s t 3 n N (u N, v) ω)
        (fun N v ω => Step1.aprioriRhs (band d) E s t n N (u N, v) ω)) :
    Step1.NetLift (P d) s t (Step1.loopInd (sample d) E s t n)
      (Step1.aprioriRhs (band d) E s t n) := by
  have hm0 : 0 < (mE E).im := mE_im_pos hE
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  set A : ℝ := 2 * (c * ((n : ℝ) + 1) + (n : ℝ) + 3) with hAdef
  have hA2 : A / 2 = c * ((n : ℝ) + 1) + (n : ℝ) + 3 := by rw [hAdef]; ring
  have hA0 : (0 : ℝ) ≤ A := by rw [hAdef]; positivity
  have hAc : -A < -c := by rw [hAdef]; nlinarith
  refine netLift_of_relaxed (P := P d) (s := s) (t := t) hst (T := 1) one_pos
    (fun N => by linarith [hs0 N, ht1 N]) (A := A) (B := (n : ℝ) - 1) hA0 hrel
    (highProb_norm_Xmat_le d) (rpow_neg_le_aprioriRhs (band d) hE hs0 hst ht1 hn) ?_
  filter_upwards [hreg, eventually_master_small (n := n) (c := c) (m0 := (mE E).im) hm0 hA2,
    eventually_const_mul_rpow_le_rpow (2 * ((n - 1 : ℕ) : ℝ)) hAc, eventually_ge_atTop 1]
    with N hregN hmaster hκ2 hN1
  intro ω hω u u' hd v
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have ht0 : (0 : ℝ) ≤ t N := le_trans (hs0 N) (hst N)
  have hηt : 0 < etaT E (t N) := etaT_pos_of_lt_one' hE (ht1 N)
  set q : ℝ := (etaT E (t N))⁻¹ with hqdef
  have hq1 : (1 : ℝ) ≤ q := one_le_inv_etaT hE ht0 (ht1 N)
  have hq0 : (0 : ℝ) < q := by linarith
  -- (2): slow variation of the right side
  have hsv : Step1.aprioriRhs (band d) E s t n N (u', v) ω
      ≤ 2 * Step1.aprioriRhs (band d) E s t n N (u, v) ω := by
    refine aprioriRhs_le_two_mul (band d) hE hs0 hst ht1 hn (ε := (N : ℝ) ^ (-A)) ?_ u u' hd v ω
    exact hκ2.trans hregN
  refine ⟨?_, hsv⟩
  -- the master bound at `η = η_{t_N}`
  have hηlow : (N : ℝ) ^ (-c) * (mE E).im ≤ etaT E (t N) := by
    show _ ≤ (1 - t N) * (mE E).im
    exact mul_le_mul_of_nonneg_right hregN hm0.le
  have hMB := hmaster (etaT E (t N)) hηt hηlow
  rw [← hqdef] at hMB
  -- `√|u-u'| ≤ N^{-A/2}`
  have hsqrt : Real.sqrt |(u : ℝ) - (u' : ℝ)| ≤ (N : ℝ) ^ (-(A / 2)) := by
    refine (Real.sqrt_le_sqrt hd).trans (le_of_eq ?_)
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (Nat.cast_nonneg N)]
    congr 1
    ring
  set X : ℝ := ‖Xmat d N ω‖ with hXdef
  have hXN : X ≤ (N : ℝ) := hω
  set Δ : ℝ := q * q * (X + 1) * Real.sqrt |(u : ℝ) - (u' : ℝ)| with hΔdef
  have hΔ0 : 0 ≤ Δ := by rw [hΔdef]; positivity
  have hΔle : Δ ≤ q * q * ((N : ℝ) + 1) * (N : ℝ) ^ (-(A / 2)) := by
    rw [hΔdef]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) hsqrt
      (Real.sqrt_nonneg _) (by positivity)
  have hqq : q * q * ((N : ℝ) + 1) * (N : ℝ) ^ (-(A / 2))
      ≤ (n : ℝ) * q ^ (n + 1) * ((N : ℝ) + 1) * (N : ℝ) ^ (-(A / 2)) := by
    have hpow : q * q ≤ (n : ℝ) * q ^ (n + 1) := by
      have h1 : q ^ 2 ≤ q ^ (n + 1) := pow_le_pow_right₀ hq1 (by omega)
      have h2 : q ^ 2 = q * q := by ring
      nlinarith [pow_nonneg hq0.le (n + 1)]
    have hrest : (0 : ℝ) ≤ ((N : ℝ) + 1) * (N : ℝ) ^ (-(A / 2)) := by positivity
    calc q * q * ((N : ℝ) + 1) * (N : ℝ) ^ (-(A / 2))
        = (q * q) * (((N : ℝ) + 1) * (N : ℝ) ^ (-(A / 2))) := by ring
      _ ≤ ((n : ℝ) * q ^ (n + 1)) * (((N : ℝ) + 1) * (N : ℝ) ^ (-(A / 2))) :=
          mul_le_mul_of_nonneg_right hpow hrest
      _ = (n : ℝ) * q ^ (n + 1) * ((N : ℝ) + 1) * (N : ℝ) ^ (-(A / 2)) := by ring
  have hΔsmall : Δ ≤ (N : ℝ) ^ (-((n : ℝ) + 1)) := (hΔle.trans hqq).trans hMB
  have hNn1 : (N : ℝ) ^ (-((n : ℝ) + 1)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN1' (by linarith)
  have hΔ1 : Δ ≤ 1 := hΔsmall.trans hNn1
  -- the entrywise modulus of the resolvent
  have hGop : ‖green (Hflow d N (u : ℝ) ω) (zt E (u : ℝ))
      - green (Hflow d N (u' : ℝ) ω) (zt E (u' : ℝ))‖ ≤ Δ :=
    norm_green_flow_sub_le_sqrt d N hE (hs0 N) (ht1 N) ω u.2 u'.2
  have hexp : -(((n : ℝ) - 1) + 2) = -((n : ℝ) + 1) := by ring
  rw [hexp]
  by_cases hωu : ω ∈ Step1.gEv (sample d) E N (u : ℝ)
  · have hmem' : ω ∈ gEvThr (sample d) E N (u' : ℝ) 3 := by
      intro i j
      have h1 : ‖green (Hflow d N (u : ℝ) ω) (zt E (u : ℝ)) i j
          - green (Hflow d N (u' : ℝ) ω) (zt E (u' : ℝ)) i j‖ ≤ Δ := by
        refine le_trans ?_ hGop
        exact norm_apply_le_l2_opNorm (green (Hflow d N (u : ℝ) ω) (zt E (u : ℝ))
          - green (Hflow d N (u' : ℝ) ω) (zt E (u' : ℝ))) i j
      have h3 : ‖green (Hflow d N (u : ℝ) ω) (zt E (u : ℝ)) i j‖ ≤ 2 := hωu i j
      have h5 := norm_sub_le (green (Hflow d N (u : ℝ) ω) (zt E (u : ℝ)) i j)
        (green (Hflow d N (u : ℝ) ω) (zt E (u : ℝ)) i j
          - green (Hflow d N (u' : ℝ) ω) (zt E (u' : ℝ)) i j)
      rw [sub_sub_cancel] at h5
      show ‖green (Hflow d N (u' : ℝ) ω) (zt E (u' : ℝ)) i j‖ ≤ 3
      linarith
    rw [Step1.loopInd, Set.indicator_of_mem hωu, loopIndThr, Set.indicator_of_mem hmem']
    have hL := norm_Lval_sub_le_sqrt d N hE (hs0 N) (ht1 N) ω u.2 u'.2 hn v
    have hLsub : ‖(sample d).Lval E N (u : ℝ) ω v.idx‖
        - ‖(sample d).Lval E N (u' : ℝ) ω v.idx‖ ≤ (n : ℝ) * (Δ * q ^ (n - 1)) := by
      refine le_trans (norm_sub_norm_le _ _) ?_
      rw [← hqdef, ← hXdef] at hL
      exact hL
    have hfin : (n : ℝ) * (Δ * q ^ (n - 1)) ≤ (N : ℝ) ^ (-((n : ℝ) + 1)) := by
      refine le_trans ?_ hMB
      have hqs : q ^ (n - 1) * (q * q) = q ^ (n + 1) := by
        rw [show q * q = q ^ 2 by ring, ← pow_add]
        congr 1
        omega
      calc (n : ℝ) * (Δ * q ^ (n - 1))
          ≤ (n : ℝ) * ((q * q * ((N : ℝ) + 1) * (N : ℝ) ^ (-(A / 2))) * q ^ (n - 1)) := by
            have := mul_le_mul_of_nonneg_right hΔle (pow_nonneg hq0.le (n - 1))
            exact mul_le_mul_of_nonneg_left this (Nat.cast_nonneg n)
        _ = (n : ℝ) * (q ^ (n - 1) * (q * q)) * (((N : ℝ) + 1) * (N : ℝ) ^ (-(A / 2))) := by
            ring
        _ = (n : ℝ) * q ^ (n + 1) * ((N : ℝ) + 1) * (N : ℝ) ^ (-(A / 2)) := by
            rw [hqs]; ring
    linarith
  · rw [Step1.loopInd, Set.indicator_of_notMem hωu]
    have h1 : 0 ≤ loopIndThr (sample d) E s t 3 n N (u', v) ω :=
      loopIndThr_nonneg _ _ _ _ _ _ _ _ _
    have h2 : (0 : ℝ) ≤ (N : ℝ) ^ (-((n : ℝ) + 1)) := Real.rpow_nonneg hN0.le _
    linarith

end NetLiftGauss


section Assembly2

open Filter MeasureTheory

/-- **`RBM.Step1.Hyp` for the Gaussian model with `lift` discharged.**  All four fields are
theorems: `scaling` is `RBM.Gauss.loopScaling_gauss` (T111), `lemma41` is
`RBM.Gauss.lemma41Flow` (T108) given the time-indexed (4.2)/(4.3), `cont` is
`RBM.Gauss.cont_gauss`, and `lift` is `RBM.Gauss.netLift_gauss` fed by
`RBM.Gauss.eq58_seq_thr` (Lemma 5.1 at threshold `3`).

Compared with `RBM.Gauss.step1Hyp_gauss`, the hypothesis `hlift` is gone; what replaces it is
(2.68)/(2.70) at `s` (`BoundsCore`) and (2.72) (`Cond272`) — which `RBM.Step1.step1` assumes
anyway — together with the regime `t_N ≤ 1 - N^{-c}`. -/
theorem step1Hyp_gauss_of_regime (d : Dims) {E κ : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ)
    {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hB : BoundsCore (sample d) E s) (hcond : Cond272 (band d) E s t)
    {c : ℝ} (hc : 0 < c) (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-c) ≤ 1 - t N)
    (hEntry : EntryBoundFlow d E s t) (hDiag : DiagBoundFlow d E s t) :
    Step1.Hyp (sample d) E s t := by
  have hE2 : |E| < 2 := by linarith
  have hS : ∀ t₁ t₂ : ℕ → ℝ, (∀ N, 1 / 2 ≤ t₁ N) → (∀ N, t₁ N ≤ t₂ N) → (∀ N, t₂ N < 1) →
      LoopScaling (sample d) E t₁ t₂ := fun t₁ t₂ h1 h12 _ =>
    loopScaling_gauss (d := d) (fun N => lt_of_lt_of_le (by norm_num : (0:ℝ) < 1/2) (h1 N)) h12
  exact
    { scaling := hS
      lift := fun n hn => netLift_gauss d hE2 hs0 hst ht1 hc hreg hn
        (fun u => eq58_seq_thr (sample d) hκ hE (C₀ := 3) (by norm_num) hB hs0 hst ht1 hcond
          hS u hn)
      lemma41 := lemma41Flow hE2 hs0 ht1 hEntry hDiag
      cont := cont_gauss d hE2 (fun N => (hs0 N)) ht1 }

/-- **The regime hypothesis of `netLift_gauss` is already a hypothesis of `RBM.Step1.step1`.**
From `N^c ≤ W ℓ_t η_t` and `W ℓ_t ≤ W L ≤ N` one gets `η_t ≥ N^{c-1} ≥ N^{-1}`, and
`η_t ≤ 1 - t_N` because `Im m ≤ 1`. -/
theorem rpow_neg_one_le_one_sub_of_scale_ge {Ωb : Type*} [MeasurableSpace Ωb] (B : Band Ωb)
    {E : ℝ} (hE : |E| < 2) {t : ℕ → ℝ} (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c)
    (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ B.scale E N (t N)) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-(1 : ℝ)) ≤ 1 - t N := by
  filter_upwards [hreg, B.dim, eventually_ge_atTop 1] with N hregN hdim hN1
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  have hW : (0 : ℝ) < B.W N := by exact_mod_cast B.W_pos N
  have hη : 0 < etaT E (t N) := etaT_pos_of_lt_one' hE (ht1 N)
  have hℓL : B.ell N (t N) ≤ (B.L N : ℝ) := min_le_right _ _
  have hWL : (B.W N : ℝ) * B.L N ≤ N := by exact_mod_cast hdim.1
  have hscale : B.scale E N (t N) ≤ (N : ℝ) * etaT E (t N) := by
    rw [Band.scale]
    calc (B.W N : ℝ) * B.ell N (t N) * etaT E (t N)
        ≤ (B.W N : ℝ) * (B.L N : ℝ) * etaT E (t N) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hℓL hW.le) hη.le
      _ ≤ (N : ℝ) * etaT E (t N) := mul_le_mul_of_nonneg_right hWL hη.le
  have hkey : (N : ℝ) ^ (c - 1) ≤ etaT E (t N) := by
    have h1 := hregN.trans hscale
    have he : (N : ℝ) ^ (c - 1) = (N : ℝ) ^ c / (N : ℝ) := by
      rw [show c - 1 = c + -(1 : ℝ) by ring, Real.rpow_add hN0, Real.rpow_neg_one,
        div_eq_mul_inv]
    rw [he, div_le_iff₀ hN0]
    linarith
  have hmono : (N : ℝ) ^ (-(1 : ℝ)) ≤ (N : ℝ) ^ (c - 1) :=
    Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
  have hm1 : (mE E).im ≤ 1 := RBM.mE_im_le_one hE
  have hm0 : 0 < (mE E).im := mE_im_pos hE
  have hlast : etaT E (t N) ≤ 1 - t N := by
    show (1 - t N) * (mE E).im ≤ 1 - t N
    nlinarith [ht1 N]
  linarith

/-- **`RBM.Step1.Hyp` for the Gaussian model under exactly the hypotheses of
`RBM.Step1.step1`.**  The regime needed by `netLift_gauss` is not an extra assumption: it is
`RBM.Step1.step1`'s own `N^c ≤ W ℓ_t η_t`.  So on top of `RBM.Step1.step1`'s hypotheses the
only inputs left are (4.2)/(4.3) along the flow (T107). -/
theorem step1Hyp_gauss_of_scale (d : Dims) {E κ : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ)
    {s t : ℕ → ℝ} (hB : BoundsCore (sample d) E s) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hcond : Cond272 (band d) E s t) {c : ℝ} (hc0 : 0 < c)
    (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale E N (t N))
    (hEntry : EntryBoundFlow d E s t) (hDiag : DiagBoundFlow d E s t) :
    Step1.Hyp (sample d) E s t :=
  step1Hyp_gauss_of_regime d hκ hE hs0 hst ht1 hB hcond one_pos
    (rpow_neg_one_le_one_sub_of_scale_ge (band d) (by linarith) ht1 hc0 hreg) hEntry hDiag

end Assembly2

end RBM.Gauss

