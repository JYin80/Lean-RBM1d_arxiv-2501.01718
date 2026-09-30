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
# Step 1 for the Gaussian model: continuity in the time and the time net

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, §5.1.

## Continuity in the time, unconditionally

For the Gaussian flow `H_u = √u X`, `z_u = E + (1-u) m`, the map `u ↦ ‖G_u - m‖_max` is
continuous on `[s_N, t_N]` for *every* sample (`continuousOn_llMax`), because
```
‖G_u - G_{u'}‖ ≤ η_u^{-1}(|√u - √u'| ‖X‖ + |u-u'|) η_{u'}^{-1}
              ≤ η_{t_N}^{-2}(‖X‖+1) |u - u'|^{1/2}      (`norm_green_flow_sub_le_sqrt`)
```
on `[s_N, t_N] ⊆ [0, t_N]`, `t_N < 1`.  No probability, no exceptional set, and in particular
`‖X‖ ≺ 1` is *not* needed — the constant is random but finite for each `ω`.

## The time net

A transfer between two dominations *both already uniform in the time* needs no time net,
because the time can be carried inside the index set.  `RBM.Step1.NetLift` is different:
`RBM.StochDom` puts the union over the index set **inside** the probability (`RBM.badSet`), so
its hypothesis — a bound along every time *sequence* — controls `P(A_{u(N)})` for one time per
`N`, while its conclusion needs `P(⋃_{u ∈ [s_N,t_N]} A_u)`.  Exactly one half of that gap is
free, and this file isolates it:

* `eventually_forall_measure_slice_le` — **free**: a choice of one time per `N` *is* a sequence,
  so the failure bound holds simultaneously for every `N`-dependent choice `θ(N) : W(N) → [s,t]`.
  (A `by_contra` plus `Classical.choice`; no continuity, no net.)
* `stochDom_reindex_of_forall_seq` — the union over `W(N)` *inside* the probability, at the cost
  of `#W(N) ≤ N^C` (`RBM.StochDom.of_forall_le`).
* `stochDom_of_forall_seq_relaxed` — the uncountable union, by the `N^{-(A+1)}`-net of (5.46)
  (`RBM.Gauss.netTime`, `netTimeIcc`) plus `RBM.Gauss.stochDom_of_subset_highProb`.
* `netLift_of_relaxed` — the `RBM.Step1.NetLift` producer.

`netLift_of_relaxed` allows the net points to carry a **relaxed** family `(ξ', ζ')`.  That is
not a luxury: the family of (5.8) carries the indicator `1(‖G_u‖_max ≤ 2)`, which is *not*
continuous in `u`, so `ξ` at `u` is never controlled by `ξ` at a net point — `‖G_{u'}‖_max` is
only `≤ 2 + o(1)`.  This is the gap that `RBM1D/Hierarchy/Step1.lean` already records in its
deviations ("the paper's net argument implicitly uses Lemma 5.1 with threshold `2 + o(1)` at the
net points").  `netLift_of_relaxed` reduces the lift to exactly that: a `≺`-bound **along time
sequences** for the family with the raised threshold.

## Main results

* `continuousOn_of_sqrt_modulus`, `self_le_sqrt_of_le_one` — generic real analysis.
* `norm_green_flow_sub_le_sqrt`, `abs_llMax_sub_le_sqrt`, `continuousOn_llMax`,
  `highProb_norm_Xmat_le` — the Gaussian side.
* `eventually_forall_measure_slice_le`, `stochDom_reindex_of_forall_seq`, `netTimeIcc`,
  `stochDom_of_forall_seq_relaxed`, `netLift_of_relaxed` — the `NetLift` machinery (generic in
  `(Ω, P)`; nothing Gaussian).

## What the lift needs

On top of `netLift_of_relaxed`: (i) a modulus in `u` for `‖L_{u,σ,a}‖`; (ii) the slow variation
`ζ(u') ≤ 2 ζ(u)` of `RBM.Step1.aprioriRhs`, which for the exponent `n - 1` needs the net spacing
below `c_n (1 - t_N)` and hence a regime hypothesis; (iii) the polynomial lower bound
`N^{-B} ≤ ζ`, i.e. `W ℓ_u η_u ≤ N^{B/(n-1)}`; and (iv) Lemma 5.1 at the threshold `2 + o(1)`.
The section "The ingredients of the lift" at the end of this file treats them.

## Deviations from the paper

The indicator of (5.8) is not continuous in `u`, so the paper's one-line net argument in the
proof of Lemma 5.1 (§5.1) is *not* the net argument for the family it is applied to; the
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
`‖X‖ ≤ N`.  This is `RBM.Gauss.stochDom_norm_Xmat_gauss` (`‖X‖ ≺ 1`, unconditional) at
`τ = 1`; on it the modulus of `norm_green_flow_sub_le_sqrt` becomes
`η_t^{-2}(N+1)|u-u'|^{1/2}`, which is the `Ξ` that `netLift_of_relaxed` wants. -/
theorem highProb_norm_Xmat_le (d : Dims) :
    HighProb (P d) (fun N => {ω | ‖Xmat d N ω‖ ≤ (N : ℝ)}) := by
  refine ((stochDom_norm_Xmat_gauss d).highProb one_pos).mono
    (Eventually.of_forall fun N ω hω => ?_)
  have h := hω ()
  simpa [Real.rpow_one] using h

/-! ### `lift`: what a bound along every time sequence does and does not give -/

section NetLift

variable {Ωb : Type*} [MeasurableSpace Ωb] {P : Measure Ωb} {s t : ℕ → ℝ}

/-- **The half of `RBM.Step1.NetLift` that is free.**  A `≺`-bound along *every* time sequence
`u(N) ∈ [s_N, t_N]` already gives the failure bound **uniformly over an `N`-dependent choice of
times**: for any family of maps `θ(N) : W(N) → [s_N, t_N]`, eventually in `N` *every* `θ(N,w)`
obeys the failure bound at level `D`.

This is the observation that the time may be carried inside the index set: a choice of one time
per `N` *is* a sequence, so no net and no
continuity are needed. What is *not* free is the union over `w` **inside** the probability — that is
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

section Assembly

end Assembly

/-! ## The ingredients of the lift

The four items of "What the lift needs":

* **(1)** the modulus in `u` of `‖L_{u,σ,a}‖`: `norm_gchain_sub_le` (a telescoping estimate for
  `RBM.gchain`, deterministic), `norm_gloop_sub_le`, and its Gaussian form
  `norm_Lval_sub_le_sqrt` — `|L_u - L_{u'}| ≤ n η_t^{-(n+1)}(‖X‖+1)|u-u'|^{1/2}`.
* **(2)** the slow variation `ζ(u') ≤ 2 ζ(u)`: `aprioriRhs_eq` shows that the right side of
  (5.8) is `(ℓ_s W η_u)^{-n+1}`, i.e. depends on `u` **only through `η_u`** (the two factors
  `ℓ_u` cancel), and `aprioriRhs_le_two_mul` is then Bernoulli's inequality — it needs the net
  spacing below `(1-t_N)/(2(n-1))`, the regime hypothesis.
* **(3)** the polynomial lower bound `N^{-(n-1)} ≤ ζ`, because `ℓ_s W η_u ≤ W L ≤ N`.
* **(4)** Lemma 5.1 at the threshold `2 + o(1)`: the threshold `2` is a *proof constant* of
  §6, not a structural one.

The **regime** `∃ c > 0, t_N ≤ 1 - N^{-c}` is the paper's own `t ≤ 1 - N^{-1+τ}`: without it
the net spacing cannot be made small compared with `1 - t_N`, and both the threshold shift and
the slow variation fail.  It follows (with `c = 1`) from `N^c ≤ W ℓ_t η_t`, since
`W ℓ_t ≤ W L ≤ N`.
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

/-- **The left side of (5.8) with the threshold raised to `C₀`**: `1(‖G_u‖_max ≤ C₀)|L_{u,σ,a}|`.
`C₀ = 2` is `RBM.Step1.loopInd`. -/
noncomputable def loopIndThr (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) (C₀ : ℝ) (n : ℕ) :
    ∀ N, RBM.TimeIcc s t N × LoopData (B.L N) n → Ωb → ℝ :=
  fun N p ω => (gEvThr X E N (p.1 : ℝ) C₀).indicator (fun ω => ‖X.Lval E N (p.1 : ℝ) ω p.2.idx‖) ω

theorem loopIndThr_nonneg (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) (C₀ : ℝ) (n N : ℕ)
    (p : RBM.TimeIcc s t N × LoopData (B.L N) n) (ω : Ωb) :
    0 ≤ loopIndThr X E s t C₀ n N p ω :=
  Set.indicator_nonneg (fun _ _ => norm_nonneg _) ω

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

end NetLiftGauss


section Assembly2

open Filter MeasureTheory

end Assembly2

end RBM.Gauss

