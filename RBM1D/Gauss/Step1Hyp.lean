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

## What is not done

`lift` itself.  Closing it needs, on top of `netLift_of_relaxed`: (i) a modulus in `u` for
`‖L_{u,σ,a}‖` (a telescoping estimate for `RBM.gloop`, not available — `Gauss/Envelope.lean`
only has the envelope `‖L‖ ≤ η_t^{-n} W^{-n+1}` and the difference against a *fixed* kernel);
(ii) the slow variation `ζ(u') ≤ 2 ζ(u)` of `RBM.Step1.aprioriRhs`, which for the exponent
`n - 1` needs the net spacing below `c_n (1 - t_N)` and hence a regime hypothesis
(the `Φ`-version is `RBM.Gauss.step1Phi_eq` and the slow-variation section of
`Gauss/Lemma41FlowGauss.lean`); (iii) the polynomial lower bound `N^{-B} ≤ ζ`, i.e.
`W ℓ_u η_u ≤ N^{B/(n-1)}`; and (iv) Lemma 5.1 at the threshold `2 + o(1)`.

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
theorem step1Hyp_gauss (d : Dims) {E : ℝ} (hE : |E| < 2) {s t : ℕ → ℝ} (hs0 : ∀ N, 0 < s N)
    (ht1 : ∀ N, t N < 1) (hEntry : EntryBoundFlow d E s t) (hDiag : DiagBoundFlow d E s t)
    (hlift : ∀ n : ℕ, 1 ≤ n → Step1.NetLift (P d) s t
      (Step1.loopInd (sample d) E s t n) (Step1.aprioriRhs (band d) E s t n)) :
    Step1.Hyp (sample d) E s t where
  scaling := fun t₁ t₂ h1 h12 _ =>
    loopScaling_gauss (d := d) (fun N => lt_of_lt_of_le (by norm_num : (0:ℝ) < 1/2) (h1 N)) h12
  lift := hlift
  lemma41 := lemma41Flow hE hs0 ht1 hEntry hDiag
  cont := cont_gauss d hE (fun N => (hs0 N).le) ht1

end Assembly

end RBM.Gauss

