/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.Step45
import RBM1D.Loop.ContinuityAssembly
import RBM1D.Defs.StochDomHighProb
import RBM1D.Gauss.APrimeGeneralMovingCarrierCore

/-!
# Step 1 of the proof of Theorem 2.21: (2.73) and (2.74)

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, §5.1 (pp. 51–52): the a priori loop
bound (2.73) `|L_{u,σ,a}| ≺ (ℓ_u/ℓ_s)^{n-1} (W ℓ_u η_u)^{-n+1}` and the weak local law (2.74)
`‖G_u - m‖_max ≺ (W ℓ_u η_u)^{-1/4}`, uniformly in `u ∈ [s, t]`.

## Generic results (any `(Ω, P)`, any parameter type)

* `forbidden_region` — **the forbidden-region argument of (5.9)**: if `1(x ≤ b) x ≺ f` and
  `f ≤ N^{-ε} a` (`a > 0`), then w.h.p. `x < a ∨ x > b` for all parameters simultaneously.
* `lt_of_forall_ne_of_continuousOn` — the deterministic core of the continuity argument
  (intermediate value theorem); `bootstrap` — its high-probability version: continuity in
  `u` (w.h.p.), the forbidden region (w.h.p.) and the initial bound at `u = s` (w.h.p.) give
  `M(u) < a(u)` for all `u ∈ [s,t]` (w.h.p.).
* `stochDom_of_highProb`, `stochDom_of_indicator` (a parameter-dependent indicator is removed
  if its events hold for all parameters simultaneously w.h.p.), `stochDom_of_forall_or`
  (case splits pointwise in `(N, u, ω)`), `stochDom_of_le_const_mul`,
  `stochDom_of_le_left_eventually`.
* `forb_arith`, `init_arith` — the real inequalities behind "`≪`" in (5.9).

## The flow

* `llMax` (`‖G_u - m‖_max`), `gEv` (the event (5.6) `‖G_u‖_max ≤ 2` at one time), `goodEv`
  (`‖G_u - m‖_max ≤ (W ℓ_u η_u)^{-1/6}`); `mem_gEv_of_llMax_le_one`, `goodEv_subset_gEv`.
* `norm_Lval_le_of_le_half` — **(5.2)** for `0 < u ≤ 1/2`:
  `|L_{u,σ,a}| ≤ (2/Im m)^n (W ℓ_u η_u)^{-n+1}` (from `RBM.norm_gloop_le_of_le_abs_im`).
* `eq54` — **(5.4)** from (2.68) and (2.59) (`RBM.stochDom_norm_Lval_of_LmK`).
* `startTime s = max(s, 1/2)`, `eq55` — **(5.5)** at `t₁ = max(s, 1/2)`: from (5.4) if
  `s ≥ 1/2` (Case 2), from (5.2) at `t = 1/2` if `s < 1/2` (Case 3).
* `eq58_seq` — **(5.8)** along a time sequence `u(N) ∈ [s,t]`: **the three-case split** is done
  pointwise in `N`: if `u ≥ t₁` apply Lemma 5.1 (`RBM.lemma_5_1'`) from `t₁` to `u` (Cases 2
  and 3; `ℓ_{t₁} ≥ ℓ_s`); otherwise `u < 1/2` and (5.2) applies (Case 1).
* `NetLift` (hypothesis predicate), `loopInd`, `aprioriRhs`, `eq58` — (5.8) uniformly in `u`.
* `Lemma41Flow` (hypothesis predicate) — Lemma 4.1 along the flow, bound-transfer form.
* `eventually_scale_facts` — from (2.72) and `W ℓ_t η_t ≥ N^c`: `N^c ≤ W ℓ_u η_u` and
  `(ℓ_u/ℓ_s)² ≤ (W ℓ_u η_u)^{1/4}` for `u ∈ [s,t]`.
* `weakLaw_highProb` — **(5.9) + the continuity argument**: w.h.p., for all `u ∈ [s,t]`,
  `‖G_u - m‖_max < (W ℓ_u η_u)^{-1/4}`.
* `Hyp` — the random-layer inputs of Step 1 bundled.
* `weakLaw` — **(2.74)**, `apriori` — **(2.73)**, in exactly the shapes of the fields
  `RBM.Steps.weakLaw` and `RBM.Steps.apriori`; `step1` — both.

## Hypotheses (never axioms)

* `RBM.BoundsCore X E s` — (2.68), (2.70) at time `s` (the hypotheses of Theorem 2.21 that
  Step 1 uses; (2.69) and (2.71) are not used), (2.72) (`RBM.Cond272`), `|E| ≤ 2 - κ`,
  `0 < s ≤ t < 1`.
* The regime `W ℓ_t η_t ≥ N^c` for some `c > 0` (see Deviations).
* `Hyp.scaling` — (6.1) (`RBM.LoopScaling`), the input of Lemma 5.1, for `1/2 ≤ t₁ ≤ t₂ < 1`.
* `Hyp.lift` — the continuity argument of p. 51 ("`N^{-C}` net + (5.1)") for the family of
  (5.8): bounds along every time sequence give bounds uniform in `u` (`NetLift`).
* `Hyp.lemma41` — Lemma 4.1 (4.2)+(4.3) at the times `u ∈ [s,t]` on
  `{‖G_u - m‖_max ≤ (W ℓ_u η_u)^{-1/6}}` (`Lemma41Flow`).
* `Hyp.cont` — the time continuity behind (5.1): w.h.p. `u ↦ ‖G_u - m‖_max` is continuous on
  `[s, t]`.

## Deviations from the paper

* **Regime.** "`≪`" in (5.9) needs `W ℓ_u η_u ≥ N^c`; (2.72) alone only gives
  `W ℓ_t η_t ≥ 1`.  We assume `W ℓ_t η_t ≥ N^c` eventually (in the application on p. 24,
  `(W ℓ_t η_t)^{-1} ≤ W^{-30τ'}`).  All three cases are also stated for time sequences
  `s(N), t(N)`, so the case split is made for each `N` (`startTime`, `eq58_seq`).
* **Case 1** is not treated separately for the weak law: (5.2) gives the (5.8)-type bound for
  `u ≤ 1/2`, and the same forbidden-region argument then covers all `u ∈ [s,t]`; the paper's
  intermediate bound (5.3) `‖G_u - m‖_max ≺ W^{-1/2}` for `u ≤ 1/2` is not derived (it is not
  needed for (2.73), (2.74)).
* **The continuity argument** is split into (i) the lifting hypothesis `NetLift` (net + union
  bound) for the loop family of (5.8), since Lemma 5.1 is proved for time *sequences*, and
  (ii) a proved intermediate-value argument (`bootstrap`) for `‖G_u - m‖_max`, whose only
  random input is continuity of `u ↦ ‖G_u - m‖_max` w.h.p.  For (ii) the forbidden region is
  obtained for all `u` simultaneously directly (the `≺` bounds are uniform in `u`).  Note that
  (i) involves the indicator `1(‖G_u‖_max ≤ 2)`, which is not continuous in `u`; the paper's
  net argument implicitly uses Lemma 5.1 with threshold `2 + o(1)` at the net points.
* **Lemma 4.1** is used in bound-transfer form with the good event
  `{‖G_u - m‖_max ≤ (W ℓ_u η_u)^{-1/6}}` (the paper's `W^{-c}`), with the right side
  `Φ_u + W⁻¹` ((4.2) contributes `W⁻¹`); `W⁻¹ ≤ (W ℓ_u η_u)⁻¹` since `ℓ_u η_u ≤ 1`.  The
  proved `RBM.entry_bound_stochDom`, `RBM.diag_bound_stochDom` are for a fixed spectral
  parameter, hence not directly applicable along `z_u`.
* In (5.9) the paper's bound `(ℓ_u/ℓ_s)^{1/2} (W ℓ_u η_u)^{-1/2}` becomes
  `((ℓ_u/ℓ_s)(W ℓ_u η_u)^{-1} + W⁻¹)^{1/2}`, and "`≪ (W ℓ_u η_u)^{-1/4}`" is made explicit via
  `(ℓ_u/ℓ_s)² ≤ (W ℓ_u η_u)^{1/4}` (from (2.72), `RBM.Step3.scale_facts_of_cond272`) with the
  gain `N^{-c/8}`.
* Lemma 5.1 is applied from `t₁ = max(s, 1/2)` (constant `c = 1/2` of Lemma 5.1), which gives
  `(ℓ_u/ℓ_{t₁})^{n-1} ≤ (ℓ_u/ℓ_s)^{n-1}`; in Case 3 the paper's "Case 2 with `s = 1/2`".
* (2.74) is proved with high probability without the `N^τ` loss
  (`‖G_u - m‖_max < (W ℓ_u η_u)^{-1/4}` for all `u`), which is stronger than `≺`.
-/

namespace RBM

open MeasureTheory Filter

namespace Step1

/-! ### Generic facts about `≺` and high probability -/

section Generic

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {U : ℕ → Type*}

/-- `N^{τ} N^{-ε} < 1` for `0 < τ < ε`, `N ≥ 2`. -/
theorem rpow_mul_rpow_neg_lt_one {N : ℕ} (hN : 2 ≤ N) {τ ε : ℝ} (hτε : τ < ε) :
    (N : ℝ) ^ τ * (N : ℝ) ^ (-ε) < 1 := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
  rw [← Real.rpow_add (by linarith)]
  exact Real.rpow_lt_one_of_one_lt_of_neg hN1 (by linarith)

/-- **The forbidden region (5.9).**  Let `x ≥ 0` be random and `f, a, b` deterministic with
`a > 0`.  If `1(x ≤ b) x ≺ f` and `f ≪ a` (i.e. `f ≤ N^{-ε} a` for some `ε > 0`), then with high
probability `x` avoids `[a, b]`, simultaneously for all parameters `u`. -/
theorem forbidden_region {x : ∀ N, U N → Ω → ℝ} {f a b : ∀ N, U N → ℝ}
    (ha : ∀ N u, 0 < a N u) {ε : ℝ} (hε : 0 < ε)
    (hfa : ∀ᶠ N : ℕ in atTop, ∀ u, f N u ≤ (N : ℝ) ^ (-ε) * a N u)
    (h : StochDom P (fun N u ω => {ω | x N u ω ≤ b N u}.indicator (fun ω => x N u ω) ω)
      (fun N u _ => f N u)) :
    HighProb P (fun N => {ω | ∀ u, x N u ω < a N u ∨ b N u < x N u ω}) := by
  refine (h.highProb (half_pos hε)).mono ?_
  filter_upwards [hfa, eventually_ge_atTop 2] with N hN hN2
  intro ω hω u
  simp only [Set.mem_ofPred_eq] at hω ⊢
  by_contra hno
  push Not at hno
  obtain ⟨hax, hxb⟩ := hno
  have h1 := hω u
  have hmem : x N u ω ≤ b N u := hxb
  rw [Set.indicator_of_mem (show ω ∈ {ω | x N u ω ≤ b N u} from hmem)] at h1
  have hpos : 0 ≤ (N : ℝ) ^ (ε / 2) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have h2 : (N : ℝ) ^ (ε / 2) * f N u ≤ (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (-ε) * a N u := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hN u) hpos
  have h3 := rpow_mul_rpow_neg_lt_one hN2 (half_lt_self hε)
  have h4 : (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (-ε) * a N u < a N u := by
    have := ha N u
    nlinarith
  linarith

/-- **The continuity argument, deterministic core.**  If `g` and `a` are continuous on
`[s, t]`, `g(s) < a(s)`, and `g(u) ≠ a(u)` for all `u ∈ [s, t]`, then `g < a` on `[s, t]`
(intermediate value theorem). -/
theorem lt_of_forall_ne_of_continuousOn {g a : ℝ → ℝ} {s t : ℝ}
    (hg : ContinuousOn g (Set.Icc s t)) (ha : ContinuousOn a (Set.Icc s t)) (h0 : g s < a s)
    (hne : ∀ u ∈ Set.Icc s t, g u ≠ a u) : ∀ u ∈ Set.Icc s t, g u < a u := by
  intro u hu
  by_contra hno
  push Not at hno
  have hsub : Set.Icc s u ⊆ Set.Icc s t := Set.Icc_subset_Icc_right hu.2
  have hc : ContinuousOn (fun v => a v - g v) (Set.Icc s u) := (ha.sub hg).mono hsub
  have h0' : (0 : ℝ) ∈ Set.Icc (a u - g u) (a s - g s) := ⟨by linarith, by linarith⟩
  obtain ⟨v, hv, hv0⟩ := intermediate_value_Icc' hu.1 hc h0'
  exact hne v (hsub hv) (by simp only at hv0; linarith)

/-- **The continuity argument (bootstrap).**  Let `M(u)` be random, continuous in `u ∈ [s,t]`
with high probability, and `a ≤ b` deterministic, `a` continuous.  If the forbidden region
`[a(u), b(u)]` is avoided for all `u` simultaneously (w.h.p.) and `M(s) < a(s)` (w.h.p.), then
`M(u) < a(u)` for all `u ∈ [s,t]` (w.h.p.). -/
theorem bootstrap {M : ∀ _ : ℕ, ℝ → Ω → ℝ} {a b : ∀ _ : ℕ, ℝ → ℝ} {s t : ℕ → ℝ}
    (hcont : HighProb P (fun N => {ω | ContinuousOn (fun u => M N u ω) (Set.Icc (s N) (t N))}))
    (ha : ∀ N, ContinuousOn (a N) (Set.Icc (s N) (t N)))
    (hab : ∀ᶠ N : ℕ in atTop, ∀ u : TimeIcc s t N, a N u ≤ b N u)
    (hforb : HighProb P (fun N => {ω | ∀ u : TimeIcc s t N, M N u ω < a N u ∨ b N u < M N u ω}))
    (hinit : HighProb P (fun N => {ω | M N (s N) ω < a N (s N)})) :
    HighProb P (fun N => {ω | ∀ u : TimeIcc s t N, M N u ω < a N u}) := by
  refine ((hcont.inter hforb).inter hinit).mono ?_
  filter_upwards [hab] with N hab
  rintro ω ⟨⟨hc, hf⟩, hi⟩
  simp only [Set.mem_ofPred_eq] at hc hf hi ⊢
  intro u
  refine lt_of_forall_ne_of_continuousOn hc (ha N) hi (fun v hv => ?_) u u.2
  rcases hf ⟨v, hv⟩ with h | h
  · exact h.ne
  · have := hab ⟨v, hv⟩
    simp only at h this
    exact (lt_of_le_of_lt this h).ne'

/-- **Removing a parameter-dependent indicator.**  If `1_{Ω(N,u)} ξ ≺ ζ` and the events
`Ω(N,u)` hold for all `u` simultaneously with high probability, then `ξ ≺ ζ`. -/
theorem stochDom_of_indicator {Ωs : ∀ N, U N → Set Ω} {ξ ζ : ∀ N, U N → Ω → ℝ}
    (hΩ : HighProb P (fun N => {ω | ∀ u, ω ∈ Ωs N u}))
    (h : StochDom P (fun N u ω => (Ωs N u).indicator (fun ω => ξ N u ω) ω) ζ) :
    StochDom P ξ ζ := by
  intro τ hτ D hD
  filter_upwards [h τ hτ (D + 1) (by linarith), hΩ (D + 1) (by linarith),
    eventually_two_mul_rpow_le D] with N h1 h2 h3
  have hsub : badSet ξ ζ τ N ⊆ badSet (fun N u ω => (Ωs N u).indicator (fun ω => ξ N u ω) ω) ζ τ N
      ∪ {ω | ∀ u, ω ∈ Ωs N u}ᶜ := by
    rintro ω ⟨u, hu⟩
    by_cases hω : ∀ u, ω ∈ Ωs N u
    · left
      refine ⟨u, ?_⟩
      simp only [Set.indicator_of_mem (hω u)]
      exact hu
    · right; exact hω
  have hp : (0 : ℝ) ≤ (N : ℝ) ^ (-(D + 1)) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  calc P (badSet ξ ζ τ N)
      ≤ P (badSet (fun N u ω => (Ωs N u).indicator (fun ω => ξ N u ω) ω) ζ τ N ∪
          {ω | ∀ u, ω ∈ Ωs N u}ᶜ) := measure_mono hsub
    _ ≤ P (badSet (fun N u ω => (Ωs N u).indicator (fun ω => ξ N u ω) ω) ζ τ N) +
          P {ω | ∀ u, ω ∈ Ωs N u}ᶜ := measure_union_le _ _
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))) + ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))) :=
        add_le_add h1 h2
    _ = ENNReal.ofReal (2 * (N : ℝ) ^ (-(D + 1))) := by
        rw [← ENNReal.ofReal_add hp hp]; ring_nf
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := ENNReal.ofReal_le_ofReal h3

/-- **Case splitting under `≺`**: if at every `(N, u, ω)` the pair `(ξ, ζ)` is dominated by
`(ξ₁, ζ₁)` or by `(ξ₂, ζ₂)` (`ξ ≤ ξᵢ`, `ζᵢ ≤ ζ`), then `ξ₁ ≺ ζ₁` and `ξ₂ ≺ ζ₂` give `ξ ≺ ζ`. -/
theorem stochDom_of_forall_or {ξ ζ ξ₁ ζ₁ ξ₂ ζ₂ : ∀ N, U N → Ω → ℝ}
    (h₁ : StochDom P ξ₁ ζ₁) (h₂ : StochDom P ξ₂ ζ₂)
    (hor : ∀ N u ω, (ξ N u ω ≤ ξ₁ N u ω ∧ ζ₁ N u ω ≤ ζ N u ω) ∨
      (ξ N u ω ≤ ξ₂ N u ω ∧ ζ₂ N u ω ≤ ζ N u ω)) : StochDom P ξ ζ := by
  refine StochDom.of_subset_union h₁ h₂ fun τ hτ => ⟨τ, hτ, Eventually.of_forall fun N => ?_⟩
  rintro ω ⟨u, hu⟩
  have hpos : 0 ≤ (N : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg N) _
  rcases hor N u ω with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨u, by nlinarith [mul_le_mul_of_nonneg_left h2 hpos]⟩
  · exact Or.inr ⟨u, by nlinarith [mul_le_mul_of_nonneg_left h2 hpos]⟩

/-- A pointwise bound `ξ ≤ C ζ` (`ξ, ζ ≥ 0`) gives `ξ ≺ ζ`. -/
theorem stochDom_of_le_const_mul {ξ ζ : ∀ N, U N → Ω → ℝ} (hξ : ∀ N u ω, 0 ≤ ξ N u ω)
    (hζ : ∀ N u ω, 0 ≤ ζ N u ω) (C : ℝ) (h : ∀ N u ω, ξ N u ω ≤ C * ζ N u ω) :
    StochDom P ξ ζ :=
  Step3.stochDom_mono hζ C (Eventually.of_forall h) (StochDom.refl hξ)

/-- A left side that is eventually pointwise smaller. -/
theorem stochDom_of_le_left_eventually {ξ ξ' ζ : ∀ N, U N → Ω → ℝ}
    (hle : ∀ᶠ N : ℕ in atTop, ∀ u ω, ξ N u ω ≤ ξ' N u ω) (h : StochDom P ξ' ζ) :
    StochDom P ξ ζ :=
  StochDom.of_subset h fun τ hτ => ⟨τ, hτ, by
    filter_upwards [hle] with N hN
    rintro ω ⟨u, hu⟩
    exact ⟨u, lt_of_lt_of_le hu (hN u ω)⟩⟩

end Generic

/-! ### The flow: `‖G_u - m‖_max`, the events, and the deterministic bound (5.2) -/

section FlowDet

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℝ}

/-- `‖G_u - m‖_max = max_{i,j} |(G_u - m)_{ij}|`. -/
noncomputable def llMax (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω) : ℝ :=
  ⨆ ij : B.Idx N × B.Idx N, X.llErr E N u ω ij

/-- The event `{‖G_u‖_max ≤ 2}` of (5.6) at a single time `u`
(`RBM.Sample.gmaxEvent X E t N = gEv X E N (t N)`). -/
def gEv (E : ℝ) (N : ℕ) (u : ℝ) : Set Ω := {ω | ∀ i j, ‖X.G E N u ω i j‖ ≤ 2}

/-- The event `{‖G_u - m‖_max ≤ (W ℓ_u η_u)^{-1/6}}` of Lemma 4.1 as used in (5.9). -/
def goodEv (E : ℝ) (N : ℕ) (u : ℝ) : Set Ω :=
  {ω | llMax X E N u ω ≤ (B.scale E N u)⁻¹ ^ ((1 : ℝ) / 6)}

theorem gmaxEvent_eq (t : ℕ → ℝ) (N : ℕ) : X.gmaxEvent E t N = gEv X E N (t N) := rfl

theorem llMax_nonneg (N : ℕ) (u : ℝ) (ω : Ω) : 0 ≤ llMax X E N u ω :=
  Real.iSup_nonneg fun _ => norm_nonneg _

theorem llErr_le_llMax (N : ℕ) (u : ℝ) (ω : Ω) (ij : B.Idx N × B.Idx N) :
    X.llErr E N u ω ij ≤ llMax X E N u ω :=
  le_ciSup (f := fun ij => X.llErr E N u ω ij) (Set.finite_range _).bddAbove ij

theorem llMax_le {N : ℕ} {u : ℝ} {ω : Ω} {c : ℝ}
    (h : ∀ ij : B.Idx N × B.Idx N, X.llErr E N u ω ij ≤ c) : llMax X E N u ω ≤ c :=
  ciSup_le h

/-- `‖G_u - m‖_max ≤ 1` implies `‖G_u‖_max ≤ 2` (`|m| = 1`). -/
theorem mem_gEv_of_llMax_le_one (hE : |E| ≤ 2) {N : ℕ} {u : ℝ} {ω : Ω}
    (h : llMax X E N u ω ≤ 1) : ω ∈ gEv X E N u := by
  intro i j
  have h1 := (llErr_le_llMax X N u ω (i, j)).trans h
  simp only [Sample.llErr] at h1
  have hm := norm_mE hE
  have h2 : ‖(mE E • (1 : Matrix (B.Idx N) (B.Idx N) ℂ)) i j‖ ≤ 1 := by
    rw [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp [hm]
  have h3 : X.G E N u ω i j = (X.G E N u ω - mE E • (1 : Matrix (B.Idx N) (B.Idx N) ℂ)) i j
      + (mE E • (1 : Matrix (B.Idx N) (B.Idx N) ℂ)) i j := by
    rw [Matrix.sub_apply]; ring
  rw [h3]
  refine (norm_add_le _ _).trans ?_
  linarith

/-- The good event of Lemma 4.1 is contained in `{‖G_u‖_max ≤ 2}` once `W ℓ_u η_u ≥ 1`. -/
theorem goodEv_subset_gEv (hE : |E| ≤ 2) {N : ℕ} {u : ℝ} (hA : 1 ≤ B.scale E N u) :
    goodEv X E N u ⊆ gEv X E N u := fun ω hω => by
  refine mem_gEv_of_llMax_le_one X hE (hω.trans ?_)
  have h0 : 0 < B.scale E N u := by linarith
  exact Real.rpow_le_one (inv_nonneg.2 h0.le) (inv_le_one_of_one_le₀ hA) (by norm_num)

/-- `W⁻¹ ≤ (W ℓ_u η_u)⁻¹` (since `ℓ_u η_u ≤ 1`). -/
theorem inv_W_le_inv_scale (hE : |E| < 2) (N : ℕ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    (B.W N : ℝ)⁻¹ ≤ (B.scale E N u)⁻¹ := by
  have hA := B.scale_pos' hE N hu0 hu1
  refine inv_anti₀ hA ?_
  have h := etaT_mul_ellHat_le (B.three_le_L N) hE.le hu0 hu1
  have hW : (0 : ℝ) ≤ B.W N := Nat.cast_nonneg _
  have : B.scale E N u = B.W N * (etaT E u * B.ell N u) := by
    simp only [Band.scale]; ring
  rw [this]
  exact mul_le_of_le_one_right hW h

/-- `1 ≤ ℓ_u / ℓ_s` for `s ≤ u < 1`. -/
theorem one_le_ell_div {N : ℕ} {s u : ℝ} (hsu : s ≤ u) (hu1 : u < 1) :
    1 ≤ B.ell N u / B.ell N s := by
  have hL : 1 ≤ B.L N := by have := B.three_le_L N; omega
  have hℓs := Step3.ellHat_pos_of_lt_one (L := B.L N) hL (hsu.trans_lt hu1)
  simp only [Band.ell]
  rw [le_div_iff₀ hℓs, one_mul]
  exact Step3.ellHat_mono hsu hu1

/-- **(5.2) in the form used by Case 1**: for `0 < u ≤ 1/2`,
`|L_{u,σ,a}| ≤ (2 / Im m)^n (W ℓ_u η_u)^{-n+1}` — from `‖G_u‖_op ≤ η_u⁻¹`, `‖E_a‖_op ≤ W⁻¹`
(`RBM.norm_gloop_le_of_le_abs_im`), `η_u ≥ Im m / 2` and `W⁻¹ ≤ (W ℓ_u η_u)⁻¹`. -/
theorem norm_Lval_le_of_le_half (hE : |E| < 2) (N : ℕ) {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2)
    (ω : Ω) {n : ℕ} (hn : 1 ≤ n) (v : LoopData (B.L N) n) :
    ‖X.Lval E N u ω v.idx‖ ≤ (2 / (mE E).im) ^ n * (B.scale E N u)⁻¹ ^ (n - 1) := by
  have hm := mE_im_pos hE
  have hu1 : u < 1 := by linarith
  have hη : (mE E).im / 2 ≤ |(zt E u).im| := by
    rw [← etaT_eq_zt_im, abs_of_pos (etaT_pos hE hu1), etaT]
    nlinarith
  have h := norm_gloop_le_of_le_abs_im (L := B.L N) (W := B.W N) (X.hermitian N u ω)
    (by positivity) hη v.idx (by simp [LoopData.idx]) (by simp [LoopData.idx, hn])
  have hlen : v.idx.a.length = n := by simp [LoopData.idx]
  rw [hlen] at h
  refine h.trans ?_
  have hW := inv_W_le_inv_scale (B := B) hE N hu0 hu1
  have hW0 : (0 : ℝ) ≤ (B.W N : ℝ)⁻¹ := inv_nonneg.2 (Nat.cast_nonneg _)
  rw [show ((mE E).im / 2)⁻¹ = 2 / (mE E).im by field_simp]
  gcongr

/-- The scale `u ↦ W ℓ_u η_u` is continuous on `[a, b]` for `b < 1`. -/
theorem continuousOn_scale (N : ℕ) {a b : ℝ} (hb : b < 1) :
    ContinuousOn (fun u => B.scale E N u) (Set.Icc a b) := by
  simp only [Band.scale, Band.ell, ellHat, etaT]
  refine ContinuousOn.mul (ContinuousOn.mul continuousOn_const ?_) (by fun_prop)
  refine ContinuousOn.inf ?_ continuousOn_const
  refine ContinuousOn.div continuousOn_const (by fun_prop) fun u hu => ?_
  have : (1 : ℂ) - (u : ℂ) = ((1 - u : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.norm_real, Real.norm_eq_abs]
  exact (Real.sqrt_pos.2 (abs_pos.2 (by linarith [hu.2]))).ne'

end FlowDet

/-! ### (5.4), (5.5), (5.8): the loop bound through Lemma 5.1 -/

section Eq58

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}

/-- The initial time `t₁ = max(s, 1/2)` at which Lemma 5.1 is applied: `t₁ = s` in Case 2
(`s ≥ 1/2`), `t₁ = 1/2` in Case 3 (`s < 1/2`). -/
noncomputable def startTime (s : ℕ → ℝ) (N : ℕ) : ℝ := max (s N) (1 / 2)

/-- `W ℓ_s η_s ≥ 1` for large `N`, from (2.72). -/
theorem eventually_one_le_scale_s (hE : |E| < 2) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hc : Cond272 B E s t) : ∀ᶠ N : ℕ in atTop, 1 ≤ B.scale E N (s N) := by
  filter_upwards [hc] with N hN
  exact (Step3.scale_facts_of_cond272 (by exact_mod_cast B.W_pos N) (B.one_le_L N) hE le_rfl
    (hst N) (ht1 N) hN).1

/-- **(5.4)**: (2.68) and (2.59) give `max_{σ,a} |L_{s,σ,a}| ≺ (W ℓ_s η_s)^{-n+1}`
(`RBM.stochDom_norm_Lval_of_LmK`). -/
theorem eq54 {κ : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) (hB : BoundsCore X E s)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hc : Cond272 B E s t)
    {n : ℕ} (hn : 1 ≤ n) :
    StochDom B.P (fun N (v : LoopData (B.L N) n) ω => ‖X.Lval E N (s N) ω v.idx‖)
      (fun N _ _ => (B.scale E N (s N))⁻¹ ^ (n - 1)) := by
  have hE2 : |E| < 2 := by linarith
  have hk0 : 0 < min κ 1 := lt_min hκ one_pos
  have hEk : |E| ≤ 2 - min κ 1 := hE.trans (by linarith [min_le_left κ 1])
  exact stochDom_norm_Lval_of_LmK X hk0 (min_le_right κ 1) hEk (fun N => (hs0 N))
    (fun N => (hst N).trans_lt (ht1 N)) (eventually_one_le_scale_s hE2 hst ht1 hc) hn
    (hB.LmK n hn)

/-- **(5.2) as a `≺` bound at the time `1/2`**. -/
theorem eq52_half (hE : |E| < 2) {n : ℕ} (hn : 1 ≤ n) :
    StochDom B.P (fun N (v : LoopData (B.L N) n) ω => ‖X.Lval E N (1 / 2) ω v.idx‖)
      (fun N _ _ => (B.scale E N (1 / 2))⁻¹ ^ (n - 1)) :=
  stochDom_of_le_const_mul (fun _ _ _ => norm_nonneg _)
    (fun N _ _ => pow_nonneg (inv_nonneg.2 (B.scale_nonneg E N (by norm_num))) _)
    ((2 / (mE E).im) ^ n)
    (fun N v ω => norm_Lval_le_of_le_half X hE N (by norm_num) le_rfl ω hn v)

/-- **(5.5) at `t₁ = max(s, 1/2)`**: `max_{σ,a} |L_{t₁,σ,a}| ≺ (W ℓ_{t₁} η_{t₁})^{-n+1}`, from
(5.4) when `s ≥ 1/2` (Case 2) and from (5.2) when `s < 1/2` (Case 3: "(5.2) holds for
`t = 1/2`"). -/
theorem eq55 {κ : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) (hB : BoundsCore X E s)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hc : Cond272 B E s t) :
    ∀ n : ℕ, 1 ≤ n → StochDom B.P
      (fun N (v : LoopData (B.L N) n) ω => ‖X.Lval E N (startTime s N) ω v.idx‖)
      (fun N _ _ => (B.scale E N (startTime s N))⁻¹ ^ (n - 1)) := by
  intro n hn
  have hE2 : |E| < 2 := by linarith
  refine stochDom_of_forall_or (eq54 X hκ hE hB hs0 hst ht1 hc hn) (eq52_half X hE2 hn)
    fun N v ω => ?_
  rcases le_total (1 / 2) (s N) with h | h
  · left
    simp only [startTime, max_eq_left h, le_refl, and_self]
  · right
    simp only [startTime, max_eq_right h, le_refl, and_self]

/-- **(5.8) along a time sequence** `u(N) ∈ [s, t]`:
`1(‖G_u‖_max ≤ 2) max_{σ,a} |L_{u,σ,a}| ≺ (ℓ_u/ℓ_s)^{n-1} (W ℓ_u η_u)^{-n+1}`.
For `u ≥ t₁ = max(s, 1/2)` this is Lemma 5.1 (`RBM.lemma_5_1'`) started at `t₁` with (5.5);
for `u < t₁` necessarily `u < 1/2` (Case 1, and the part `[s, 1/2]` of Case 3), and it is the
deterministic bound (5.2). -/
theorem eq58_seq {κ : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) (hB : BoundsCore X E s)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hc : Cond272 B E s t)
    (hS : ∀ t₁ t₂ : ℕ → ℝ, (∀ N, 1 / 2 ≤ t₁ N) → (∀ N, t₁ N ≤ t₂ N) → (∀ N, t₂ N < 1) →
      LoopScaling X E t₁ t₂)
    (u : ∀ N, TimeIcc s t N) {n : ℕ} (hn : 1 ≤ n) :
    StochDom B.P (fun N (v : LoopData (B.L N) n) ω =>
        (gEv X E N (u N)).indicator (fun ω => ‖X.Lval E N (u N) ω v.idx‖) ω)
      (fun N _ _ => (B.ell N (u N) / B.ell N (s N)) ^ (n - 1) *
        (B.scale E N (u N))⁻¹ ^ (n - 1)) := by
  have hE2 : |E| < 2 := by linarith
  have h1 : ∀ N, 1 / 2 ≤ startTime s N := fun N => le_max_right _ _
  have h12 : ∀ N, startTime s N ≤ max (u N : ℝ) (startTime s N) := fun N => le_max_right _ _
  have h2 : ∀ N, max (u N : ℝ) (startTime s N) < 1 := fun N =>
    max_lt ((u N).2.2.trans_lt (ht1 N)) (max_lt ((hst N).trans_lt (ht1 N)) (by norm_num))
  have h51 := lemma_5_1' X hκ hE (c := 1 / 2) (by norm_num) h1 h12 h2
    (hS _ _ h1 h12 h2) (eq55 X hκ hE hB hs0 hst ht1 hc) n hn
  set C : ℝ := (2 / (mE E).im) ^ n with hC
  have hm := mE_im_pos hE2
  have hC0 : 0 ≤ C := by positivity
  have hu0 : ∀ N, (0 : ℝ) ≤ (u N : ℝ) := fun N => (hs0 N).trans (u N).2.1
  have hu1 : ∀ N, (u N : ℝ) < 1 := fun N => (u N).2.2.trans_lt (ht1 N)
  have hζ0 : ∀ N, 0 ≤ (B.ell N (u N) / B.ell N (s N)) ^ (n - 1) *
      (B.scale E N (u N))⁻¹ ^ (n - 1) := fun N => by
    have h := one_le_ell_div (B := B) (N := N) (u N).2.1 (hu1 N)
    have := (B.scale_pos' hE2 N (hu0 N) (hu1 N))
    positivity
  have hdet : StochDom B.P
      (fun N (_ : LoopData (B.L N) n) (_ : Ω) => C * ((B.ell N (u N) / B.ell N (s N)) ^ (n - 1) *
        (B.scale E N (u N))⁻¹ ^ (n - 1)))
      (fun N _ _ => (B.ell N (u N) / B.ell N (s N)) ^ (n - 1) *
        (B.scale E N (u N))⁻¹ ^ (n - 1)) :=
    stochDom_of_le_const_mul (fun N _ _ => mul_nonneg hC0 (hζ0 N)) (fun N _ _ => hζ0 N) C
      fun _ _ _ => le_rfl
  refine stochDom_of_forall_or h51 hdet fun N v ω => ?_
  by_cases h : startTime s N ≤ u N
  · left
    have ht2 : max (u N : ℝ) (startTime s N) = u N := max_eq_left h
    refine ⟨by simp only [gmaxEvent_eq, ht2, le_refl], ?_⟩
    simp only [ht2]
    have hL : 1 ≤ B.L N := B.one_le_L N
    have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
    have hℓs := Step3.ellHat_pos_of_lt_one (L := B.L N) hL hs1
    have hℓu := Step3.ellHat_pos_of_lt_one (L := B.L N) hL (hu1 N)
    have hmono : ellHat (B.L N) ((s N : ℝ) : ℂ) ≤ ellHat (B.L N) ((startTime s N : ℝ) : ℂ) :=
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
    have hind : (gEv X E N (u N)).indicator (fun ω => ‖X.Lval E N (u N) ω v.idx‖) ω ≤
        ‖X.Lval E N (u N) ω v.idx‖ := Set.indicator_le_self' (fun _ _ => norm_nonneg _) ω
    refine hind.trans ((norm_Lval_le_of_le_half X hE2 N (hu0 N) hhalf ω hn v).trans ?_)
    rw [← hC]
    have hR := one_le_pow₀ (n := n - 1) (one_le_ell_div (B := B) (N := N) (u N).2.1 (hu1 N))
    have hA := (B.scale_pos' hE2 N (hu0 N) (hu1 N))
    have hA' : 0 ≤ (B.scale E N (u N))⁻¹ ^ (n - 1) := by positivity
    have := mul_le_mul_of_nonneg_right hR hA'
    rw [one_mul] at this
    exact mul_le_mul_of_nonneg_left this hC0

/-- **The continuity argument of p. 51 ("`N^{-C}` net + (5.1)"), as a hypothesis** on a
family indexed by the times `u ∈ [s, t]` and a finite parameter `v`: a `≺`-bound along every
time sequence `u(N) ∈ [s(N), t(N)]` (uniform in `v`) implies the bound uniformly in
`(u, v)`.  In the paper this is the union bound over an `N^{-C}`-net of `[s, t]` plus the time
continuity (5.1) of `G_u` (Gaussian flow, up to exponentially small events). -/
def NetLift (P : Measure Ω) (s t : ℕ → ℝ) {V : ℕ → Type*}
    (ξ ζ : ∀ N, TimeIcc s t N × V N → Ω → ℝ) : Prop :=
  (∀ u : ∀ N, TimeIcc s t N,
    StochDom P (fun N v ω => ξ N (u N, v) ω) (fun N v ω => ζ N (u N, v) ω)) →
  StochDom P ξ ζ

/-- The left side of (5.8): `1(‖G_u‖_max ≤ 2) |L_{u,σ,a}|`, `u ∈ [s,t]`, `(σ, a)` of length `n`. -/
noncomputable def loopInd (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) (n : ℕ) :
    ∀ N, TimeIcc s t N × LoopData (B.L N) n → Ω → ℝ :=
  fun N p ω => (gEv X E N p.1).indicator (fun ω => ‖X.Lval E N p.1 ω p.2.idx‖) ω


/-- **(5.8)** uniformly in `u ∈ [s, t]` (all three cases at once):
`1(‖G_u‖_max ≤ 2) max_{σ,a} |L_{u,σ,a}| ≺ (ℓ_u/ℓ_s)^{n-1} (W ℓ_u η_u)^{-n+1}`. -/
theorem eq58 {κ : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) (hB : BoundsCore X E s)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hc : Cond272 B E s t)
    (hS : ∀ t₁ t₂ : ℕ → ℝ, (∀ N, 1 / 2 ≤ t₁ N) → (∀ N, t₁ N ≤ t₂ N) → (∀ N, t₂ N < 1) →
      LoopScaling X E t₁ t₂)
    {n : ℕ} (hn : 1 ≤ n) (hlift : NetLift B.P s t (loopInd X E s t n) (aprioriRhs B E s t n)) :
    StochDom B.P (loopInd X E s t n) (aprioriRhs B E s t n) :=
  hlift fun u => eq58_seq X hκ hE hB hs0 hst ht1 hc hS u hn

end Eq58

/-! ### Real inequalities for (5.9) -/

section Arith

/-- `(A^{1/8})^k = A^{k/8}`. -/
theorem rpow_eighth_pow {A : ℝ} (hA : 0 ≤ A) (k : ℕ) :
    (A ^ ((1 : ℝ) / 8)) ^ k = A ^ ((k : ℝ) / 8) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hA]; ring_nf

/-- The scale identities in the variable `y = A^{1/8}`. -/
theorem rpow_facts {A : ℝ} (hA : 0 < A) :
    A = (A ^ ((1 : ℝ) / 8)) ^ 8 ∧ A ^ ((1 : ℝ) / 4) = (A ^ ((1 : ℝ) / 8)) ^ 2 ∧
      A⁻¹ ^ ((1 : ℝ) / 4) = ((A ^ ((1 : ℝ) / 8)) ^ 2)⁻¹ ∧
      A⁻¹ ^ ((1 : ℝ) / 2) = ((A ^ ((1 : ℝ) / 8)) ^ 4)⁻¹ := by
  have h8 := rpow_eighth_pow hA.le 8
  have h2 := rpow_eighth_pow hA.le 2
  have h4 := rpow_eighth_pow hA.le 4
  norm_num at h8 h2 h4
  refine ⟨h8.symm, ?_, ?_, ?_⟩
  · rw [h2]
  · rw [Real.inv_rpow hA.le, h2]
  · rw [Real.inv_rpow hA.le, h4]

/-- `N^{c/8} ≤ A^{1/8}` from `N^c ≤ A`. -/
theorem rpow_eighth_le {N : ℕ} {c A : ℝ} (h : (N : ℝ) ^ c ≤ A) :
    (N : ℝ) ^ (c / 8) ≤ A ^ ((1 : ℝ) / 8) := by
  have h1 := Real.rpow_le_rpow (Real.rpow_nonneg (Nat.cast_nonneg N) c) h
    (by norm_num : (0 : ℝ) ≤ 1 / 8)
  rwa [← Real.rpow_mul (Nat.cast_nonneg N), show c * (1 / 8) = c / 8 by ring] at h1

/-- **The arithmetic of "`f ≪ a`" in (5.9)**: with `A = W ℓ_u η_u`, `R = ℓ_u/ℓ_s`,
`R² ≤ A^{1/4}` and `2 ≤ q ≤ A^{1/8}`: `(R A⁻¹ + w)^{1/2} ≤ q⁻¹ A^{-1/4}` for `0 ≤ w ≤ A⁻¹`. -/
theorem forb_arith {A R w q : ℝ} (hA : 0 < A) (hq : 2 ≤ q) (hqA : q ≤ A ^ ((1 : ℝ) / 8))
    (hR0 : 0 ≤ R) (hR : R ^ 2 ≤ A ^ ((1 : ℝ) / 4)) (hw0 : 0 ≤ w) (hw : w ≤ A⁻¹) :
    Real.sqrt (R * A⁻¹ + w) ≤ q⁻¹ * A⁻¹ ^ ((1 : ℝ) / 4) := by
  obtain ⟨h8, h14, hi4, -⟩ := rpow_facts hA
  set y := A ^ ((1 : ℝ) / 8) with hy
  have hy0 : 0 < y := Real.rpow_pos_of_pos hA _
  have hq0 : 0 < q := by linarith
  rw [hi4]
  rw [h14] at hR
  have hRy : R ≤ y := by nlinarith
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  rw [h8] at hw ⊢
  have hy2 : 2 * q ^ 2 ≤ y ^ 3 := by
    have : q ^ 3 ≤ y ^ 3 := pow_le_pow_left₀ hq0.le hqA 3
    nlinarith
  have hlhs : R * (y ^ 8)⁻¹ + w ≤ 2 * y * (y ^ 8)⁻¹ := by
    have h1 : (y ^ 8)⁻¹ ≤ y * (y ^ 8)⁻¹ := by
      have : (1 : ℝ) ≤ y := by linarith
      have hp : 0 < (y ^ 8)⁻¹ := by positivity
      nlinarith
    have h2 : R * (y ^ 8)⁻¹ ≤ y * (y ^ 8)⁻¹ :=
      mul_le_mul_of_nonneg_right hRy (by positivity)
    linarith
  refine hlhs.trans (le_of_eq_of_le rfl ?_)
  rw [mul_pow, inv_pow, inv_pow, ← pow_mul]
  rw [show 2 * y * (y ^ 8)⁻¹ = 2 * (y ^ 7)⁻¹ by field_simp]
  rw [show (q ^ 2)⁻¹ * (y ^ (2 * 2))⁻¹ = (q ^ 2 * y ^ 4)⁻¹ by rw [mul_inv]]
  rw [show 2 * (y ^ 7)⁻¹ = (y ^ 7 / 2)⁻¹ by field_simp]
  refine inv_anti₀ (by positivity) ?_
  have : q ^ 2 * y ^ 4 * 2 ≤ y ^ 3 * y ^ 4 := by nlinarith [pow_pos hy0 4]
  have e : y ^ 7 = y ^ 3 * y ^ 4 := by ring
  rw [e]; linarith

/-- **The arithmetic of the initial bound**: `q (A⁻¹)^{1/2} < (A⁻¹)^{1/4}` for
`2 ≤ q ≤ A^{1/8}`. -/
theorem init_arith {A q : ℝ} (hA : 0 < A) (hq : 2 ≤ q) (hqA : q ≤ A ^ ((1 : ℝ) / 8)) :
    q * A⁻¹ ^ ((1 : ℝ) / 2) < A⁻¹ ^ ((1 : ℝ) / 4) := by
  obtain ⟨-, -, hi4, hi2⟩ := rpow_facts hA
  set y := A ^ ((1 : ℝ) / 8) with hy
  have hy0 : 0 < y := Real.rpow_pos_of_pos hA _
  rw [hi4, hi2]
  have hy2 : q < y ^ 2 := by nlinarith
  rw [show (y ^ 4)⁻¹ = (y ^ 2)⁻¹ * (y ^ 2)⁻¹ by rw [← mul_inv]; ring_nf]
  have hp : 0 < (y ^ 2)⁻¹ := by positivity
  have : q * (y ^ 2)⁻¹ < 1 := by
    rw [← div_eq_mul_inv, div_lt_one (by positivity)]; exact hy2
  nlinarith

end Arith

/-! ### (5.9) and (2.74): the weak local law -/

section WeakLaw

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}

/-- **Lemma 4.1, (4.2) and (4.3), for the flow at the times `u ∈ [s, t]`**, in bound-transfer
form, on the event `Ω_u = {‖G_u - m‖_max ≤ (W ℓ_u η_u)^{-1/6}}` (the paper's `Ω(t, c)`): if
`1_{Ω_u} |L_{u,(+,-),(a,b)}| ≺ Φ_u` uniformly in `u, a, b` (`Φ` deterministic), then
`1_{Ω_u} ‖G_u - m‖²_max ≺ Φ_u + W⁻¹` uniformly in `u`.  (`RBM.entry_bound_stochDom`,
`RBM.diag_bound_stochDom` prove this for a fixed spectral parameter from the large deviation
inputs; the flow needs it along `z = z_u`, `u ∈ [s,t]`, which is why it is a hypothesis.) -/
def Lemma41Flow (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) : Prop :=
  ∀ Φ : ∀ N, TimeIcc s t N → ℝ, (∀ N u, 0 ≤ Φ N u) →
    StochDom B.P (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
        (goodEv X E N p.1).indicator (fun ω => ‖X.Lval E N p.1 ω (pmLoop p.2.1 p.2.2)‖) ω)
      (fun N p _ => Φ N p.1) →
    StochDom B.P (fun N (u : TimeIcc s t N) ω =>
        (goodEv X E N u).indicator (fun ω => llMax X E N u ω ^ 2) ω)
      (fun N u _ => Φ N u + (B.W N : ℝ)⁻¹)

/-- **The scales on `[s, t]`** under (2.72) and `W ℓ_t η_t ≥ N^c`: for large `N` and all
`u ∈ [s, t]`, `N^c ≤ W ℓ_u η_u` and `(ℓ_u/ℓ_s)² ≤ (W ℓ_u η_u)^{1/4}`. -/
theorem eventually_scale_facts (hE : |E| < 2) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hc : Cond272 B E s t) {c : ℝ} (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ B.scale E N (t N)) :
    ∀ᶠ N : ℕ in atTop, ∀ u : TimeIcc s t N, (N : ℝ) ^ c ≤ B.scale E N u ∧
      (B.ell N u / B.ell N (s N)) ^ 2 ≤ B.scale E N u ^ ((1 : ℝ) / 4) := by
  filter_upwards [hc, hreg] with N hN hN'
  intro u
  have hW : (0 : ℝ) < B.W N := by exact_mod_cast B.W_pos N
  have hL := B.one_le_L N
  have hu1 : (u : ℝ) < 1 := u.2.2.trans_lt (ht1 N)
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  obtain ⟨hAs1, hAus, -, hkey⟩ :=
    Step3.scale_facts_of_cond272 hW hL hE u.2.1 u.2.2 (ht1 N) hN
  have hanti := flowScale_antitoneOn hW.le (B.L N) E (Set.mem_Iic.2 hu1.le)
    (Set.mem_Iic.2 (ht1 N).le) u.2.2
  refine ⟨hN'.trans hanti, ?_⟩
  change flowScale (B.W N) (B.L N) E u ≤ flowScale (B.W N) (B.L N) E (s N) at hAus
  set Au := flowScale (B.W N) (B.L N) E u
  set As := flowScale (B.W N) (B.L N) E (s N)
  have hAu : 0 < Au := flowScale_pos hW hL hE hu1
  have hℓs := Step3.ellHat_pos_of_lt_one (L := B.L N) hL hs1
  have hℓu := Step3.ellHat_pos_of_lt_one (L := B.L N) hL hu1
  have hRu : B.ell N u / B.ell N (s N) ≤ ellHat (B.L N) (t N : ℂ) / ellHat (B.L N) (s N : ℂ) :=
    div_le_div_of_nonneg_right (Step3.ellHat_mono u.2.2 (ht1 N)) hℓs.le
  have hR0 : 0 ≤ B.ell N u / B.ell N (s N) := div_nonneg hℓu.le hℓs.le
  have h34 : Au ^ ((3 : ℝ) / 4) ≤ As ^ ((3 : ℝ) / 4) :=
    Real.rpow_le_rpow hAu.le hAus (by norm_num)
  have hp : 0 < Au ^ ((3 : ℝ) / 4) := Real.rpow_pos_of_pos hAu _
  have hsplit : Au = Au ^ ((1 : ℝ) / 4) * Au ^ ((3 : ℝ) / 4) := by
    rw [← Real.rpow_add hAu]; norm_num
  have hR2 : (B.ell N u / B.ell N (s N)) ^ 2 ≤
      (ellHat (B.L N) (t N : ℂ) / ellHat (B.L N) (s N : ℂ)) ^ 2 := pow_le_pow_left₀ hR0 hRu 2
  have : (B.ell N u / B.ell N (s N)) ^ 2 * Au ^ ((3 : ℝ) / 4) ≤
      Au ^ ((1 : ℝ) / 4) * Au ^ ((3 : ℝ) / 4) := by
    rw [← hsplit]
    calc _ ≤ (ellHat (B.L N) (t N : ℂ) / ellHat (B.L N) (s N : ℂ)) ^ 2 * As ^ ((3 : ℝ) / 4) :=
          mul_le_mul hR2 h34 hp.le (sq_nonneg _)
      _ ≤ Au := hkey
  exact le_of_mul_le_mul_right this hp

/-- **(5.9) and the continuity argument: (2.74) holds with high probability, simultaneously
for all `u ∈ [s, t]`**: `‖G_u - m‖_max < (W ℓ_u η_u)^{-1/4}`.

Proof, as on p. 52: (5.8) at `n = 2` and Lemma 4.1 give
`1(‖G_u - m‖_max ≤ (W ℓ_u η_u)^{-1/6}) ‖G_u - m‖_max ≺ (ℓ_u/ℓ_s)^{1/2}(W ℓ_u η_u)^{-1/2}`;
by (2.72) the right side is `≪ (W ℓ_u η_u)^{-1/4}`, so `[(W ℓ_u η_u)^{-1/4}, (W ℓ_u η_u)^{-1/6}]`
is a forbidden region (`forbidden_region`); at `u = s` the assumption (2.70) puts
`‖G_s - m‖_max` below it, and continuity in `u` (`bootstrap`) keeps it there. -/
theorem weakLaw_highProb (hE : |E| < 2) (hB : BoundsCore X E s) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hc : Cond272 B E s t) {c : ℝ} (hc0 : 0 < c)
    (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ B.scale E N (t N))
    (h58 : StochDom B.P (loopInd X E s t 2) (aprioriRhs B E s t 2))
    (h41 : Lemma41Flow X E s t)
    (hcont : HighProb B.P
      (fun N => {ω | ContinuousOn (fun u => llMax X E N u ω) (Set.Icc (s N) (t N))})) :
    HighProb B.P (fun N => {ω | ∀ u : TimeIcc s t N,
      llMax X E N u ω < (B.scale E N u)⁻¹ ^ ((1 : ℝ) / 4)}) := by
  have hu0 : ∀ N (u : TimeIcc s t N), (0 : ℝ) ≤ (u : ℝ) := fun N u => (hs0 N).trans u.2.1
  have hu1 : ∀ N (u : TimeIcc s t N), (u : ℝ) < 1 := fun N u => u.2.2.trans_lt (ht1 N)
  have hA : ∀ N (u : TimeIcc s t N), 0 < B.scale E N u := fun N u =>
    B.scale_pos' hE N (hu0 N u) (hu1 N u)
  have hfacts := eventually_scale_facts hE hst ht1 hc hreg
  -- `A_u ≥ 1` for large `N`
  have hA1 : ∀ᶠ N : ℕ in atTop, ∀ u : TimeIcc s t N, 1 ≤ B.scale E N u := by
    filter_upwards [hfacts, eventually_ge_atTop 1] with N hN hN1 u
    exact (Real.one_le_rpow (by exact_mod_cast hN1) hc0.le).trans (hN u).1
  -- `q = N^{c/8} ≥ 2` for large `N`
  have hq2 : ∀ᶠ N : ℕ in atTop, (2 : ℝ) ≤ (N : ℝ) ^ (c / 8) :=
    eventually_le_rpow 2 (by positivity)
  set Φ : ∀ N, TimeIcc s t N → ℝ := fun N u =>
    B.ell N u / B.ell N (s N) * (B.scale E N u)⁻¹ with hΦdef
  have hΦ0 : ∀ N u, 0 ≤ Φ N u := fun N u => by
    have h := one_le_ell_div (B := B) (N := N) u.2.1 (hu1 N u)
    have := hA N u
    simp only [hΦdef]; positivity
  -- (5.8) at `n = 2`, for `σ = (+,-)`
  have h2 := h58.precomp_param
    (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) => (p.1, Step45.pmData p.2.1 p.2.2))
  simp only [loopInd, aprioriRhs, Step45.pmData_idx, Nat.reduceSub, pow_one] at h2
  -- the input of Lemma 4.1, on its good event
  have hin : StochDom B.P
      (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
        (goodEv X E N p.1).indicator (fun ω => ‖X.Lval E N p.1 ω (pmLoop p.2.1 p.2.2)‖) ω)
      (fun N p _ => Φ N p.1) := by
    refine stochDom_of_le_left_eventually ?_ h2
    filter_upwards [hA1] with N hN p ω
    exact Set.indicator_le_indicator_of_subset (goodEv_subset_gEv X hE.le (hN p.1))
      (fun _ => norm_nonneg _) ω
  -- Lemma 4.1, then square roots
  have hM2 := h41 Φ hΦ0 hin
  have hM := StochDom.sqrt_of
    (fun N (u : TimeIcc s t N) ω =>
      Set.indicator_nonneg (fun ω _ => sq_nonneg (llMax X E N u ω)) ω)
    (fun N (u : TimeIcc s t N) _ => add_nonneg (hΦ0 N u) (inv_nonneg.2 (Nat.cast_nonneg _))) hM2
  have hM' : StochDom B.P
      (fun N (u : TimeIcc s t N) ω => {ω | llMax X E N u ω ≤
        (B.scale E N u)⁻¹ ^ ((1 : ℝ) / 6)}.indicator (fun ω => llMax X E N u ω) ω)
      (fun N u _ => Real.sqrt (Φ N u + (B.W N : ℝ)⁻¹)) := by
    refine StochDom.of_le_left (fun N u ω => le_of_eq ?_) hM
    by_cases hω : ω ∈ goodEv X E N u
    · have hω' : ω ∈ {ω | llMax X E N u ω ≤ (B.scale E N u)⁻¹ ^ ((1 : ℝ) / 6)} := hω
      rw [Set.indicator_of_mem hω', Set.indicator_of_mem hω,
        Real.sqrt_sq (llMax_nonneg X N u ω)]
    · have hω' : ω ∉ {ω | llMax X E N u ω ≤ (B.scale E N u)⁻¹ ^ ((1 : ℝ) / 6)} := hω
      rw [Set.indicator_of_notMem hω', Set.indicator_of_notMem hω, Real.sqrt_zero]
  -- the forbidden region (5.9)
  have hforb := forbidden_region (P := B.P)
    (a := fun N (u : TimeIcc s t N) => (B.scale E N u)⁻¹ ^ ((1 : ℝ) / 4))
    (fun N u => Real.rpow_pos_of_pos (inv_pos.2 (hA N u)) _) (by positivity : 0 < c / 8)
    (by
      filter_upwards [hfacts, hq2] with N hN hq u
      obtain ⟨h1, h2⟩ := hN u
      have hqA := rpow_eighth_le h1
      have hR0 : 0 ≤ B.ell N u / B.ell N (s N) := (zero_le_one.trans
        (one_le_ell_div (B := B) (N := N) u.2.1 (hu1 N u)))
      have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      rw [Real.rpow_neg hN0]
      simp only [hΦdef]
      exact forb_arith (hA N u) hq hqA hR0 h2 (inv_nonneg.2 (Nat.cast_nonneg _))
        (inv_W_le_inv_scale hE N (hu0 N u) (hu1 N u)))
    hM'
  -- the initial condition at `u = s`, from (2.70)
  have hinit : HighProb B.P (fun N => {ω | llMax X E N (s N) ω <
      (B.scale E N (s N))⁻¹ ^ ((1 : ℝ) / 4)}) := by
    refine (hB.localLaw.highProb (by positivity : 0 < c / 8)).mono ?_
    filter_upwards [hfacts, hq2] with N hN hq ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    have hAs := hA N ⟨s N, le_rfl, hst N⟩
    have h1 := rpow_eighth_le (hN ⟨s N, le_rfl, hst N⟩).1
    exact (llMax_le X hω).trans_lt (init_arith hAs hq h1)
  -- continuity of `a(u) = (W ℓ_u η_u)^{-1/4}`
  have hacont : ∀ N, ContinuousOn (fun u => (B.scale E N u)⁻¹ ^ ((1 : ℝ) / 4))
      (Set.Icc (s N) (t N)) := fun N =>
    ((continuousOn_scale N (ht1 N)).inv₀ fun u hu =>
      (B.scale_pos' hE N ((hs0 N).trans hu.1) (hu.2.trans_lt (ht1 N))).ne').rpow_const
      fun _ _ => Or.inr (by norm_num)
  -- `a ≤ b`
  have hab : ∀ᶠ N : ℕ in atTop, ∀ u : TimeIcc s t N,
      (B.scale E N u)⁻¹ ^ ((1 : ℝ) / 4) ≤ (B.scale E N u)⁻¹ ^ ((1 : ℝ) / 6) := by
    filter_upwards [hA1] with N hN u
    exact Real.rpow_le_rpow_of_exponent_ge (inv_pos.2 (hA N u)) (inv_le_one_of_one_le₀ (hN u))
      (by norm_num)
  exact bootstrap (M := fun N u ω => llMax X E N u ω)
    (a := fun N u => (B.scale E N u)⁻¹ ^ ((1 : ℝ) / 4))
    (b := fun N u => (B.scale E N u)⁻¹ ^ ((1 : ℝ) / 6)) hcont hacont hab hforb hinit

end WeakLaw

/-! ### Step 1: (2.73) and (2.74) in the shapes of `RBM.Steps.apriori`, `RBM.Steps.weakLaw` -/

section Main

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}

/-- **The random-layer inputs of Step 1** (all hypotheses, none an axiom).
* `scaling` — (6.1), the input of Lemma 5.1 (`RBM.LoopScaling`), for start times `≥ 1/2`;
* `lift` — the continuity argument ("`N^{-C}` net + (5.1)") for the loop family of (5.8);
* `lemma41` — Lemma 4.1 (4.2)+(4.3) along the flow (`Lemma41Flow`);
* `cont` — the time continuity behind (5.1): w.h.p. `u ↦ ‖G_u - m‖_max` is continuous on
  `[s, t]` (the Gaussian flow has continuous paths). -/
structure Hyp (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) : Prop where
  scaling : ∀ t₁ t₂ : ℕ → ℝ, (∀ N, 1 / 2 ≤ t₁ N) → (∀ N, t₁ N ≤ t₂ N) → (∀ N, t₂ N < 1) →
    LoopScaling X E t₁ t₂
  lift : ∀ n : ℕ, 1 ≤ n → NetLift B.P s t (loopInd X E s t n) (aprioriRhs B E s t n)
  lemma41 : Lemma41Flow X E s t
  cont : HighProb B.P
    (fun N => {ω | ContinuousOn (fun u => llMax X E N u ω) (Set.Icc (s N) (t N))})

/-- **(2.74)** (Step 1, weak local law) in exactly the shape of `RBM.Steps.weakLaw`:
`‖G_u - m‖_max ≺ (W ℓ_u η_u)^{-1/4}`, uniformly in `u ∈ [s, t]`. -/
theorem weakLaw {κ : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) (hB : BoundsCore X E s)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hc : Cond272 B E s t)
    {c : ℝ} (hc0 : 0 < c) (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ B.scale E N (t N))
    (h : Hyp X E s t) :
    StochDom B.P
      (fun N (p : TimeIcc s t N × (B.Idx N × B.Idx N)) ω => X.llErr E N p.1 ω p.2)
      (fun N p _ => (B.scale E N p.1)⁻¹ ^ ((1 : ℝ) / 4)) := by
  have hE2 : |E| < 2 := by linarith
  have hw := weakLaw_highProb X hE2 hB hs0 hst ht1 hc hc0 hreg
    (eq58 X hκ hE hB hs0 hst ht1 hc h.scaling (by norm_num) (h.lift 2 (by norm_num)))
    h.lemma41 h.cont
  refine stochDom_of_highProb (fun N p _ => Real.rpow_nonneg (inv_nonneg.2
    (B.scale_nonneg E N (p.1.2.2.trans (ht1 N).le))) _) ?_
  refine hw.mono (Eventually.of_forall fun N ω hω p => ?_)
  simp only [Set.mem_ofPred_eq] at hω ⊢
  exact (llErr_le_llMax X N p.1 ω p.2).trans (hω p.1).le

/-- **(2.73)** (Step 1, a priori loop bound) in exactly the shape of `RBM.Steps.apriori`:
`max_{σ,a} |L_{u,σ,a}| ≺ (ℓ_u/ℓ_s)^{n-1} (W ℓ_u η_u)^{-n+1}`, uniformly in `u ∈ [s, t]`, for
every `n ≥ 1`.  (5.8) plus the removal of the indicator `1(‖G_u‖_max ≤ 2)`, which holds for
all `u` simultaneously w.h.p. by the weak law (2.74). -/
theorem apriori {κ : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) (hB : BoundsCore X E s)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hc : Cond272 B E s t)
    {c : ℝ} (hc0 : 0 < c) (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ B.scale E N (t N))
    (h : Hyp X E s t) :
    ∀ n : ℕ, 1 ≤ n → StochDom B.P
      (fun N (p : TimeIcc s t N × LoopData (B.L N) n) ω => ‖X.Lval E N p.1 ω p.2.idx‖)
      (fun N p _ => (B.ell N p.1 / B.ell N (s N)) ^ (n - 1) * (B.scale E N p.1)⁻¹ ^ (n - 1)) := by
  intro n hn
  have hE2 : |E| < 2 := by linarith
  have hw := weakLaw_highProb X hE2 hB hs0 hst ht1 hc hc0 hreg
    (eq58 X hκ hE hB hs0 hst ht1 hc h.scaling (by norm_num) (h.lift 2 (by norm_num)))
    h.lemma41 h.cont
  have hfacts := eventually_scale_facts hE2 hst ht1 hc hreg
  have hΩ : HighProb B.P (fun N => {ω | ∀ p : TimeIcc s t N × LoopData (B.L N) n,
      ω ∈ gEv X E N p.1}) := by
    refine hw.mono ?_
    filter_upwards [hfacts, eventually_ge_atTop 1] with N hN hN1 ω hω p
    simp only [Set.mem_ofPred_eq] at hω ⊢
    have hA1 : 1 ≤ B.scale E N p.1 :=
      (Real.one_le_rpow (by exact_mod_cast hN1) hc0.le).trans (hN p.1).1
    have hA0 : 0 < B.scale E N p.1 := by linarith
    refine mem_gEv_of_llMax_le_one X hE2.le ((hω p.1).le.trans ?_)
    exact Real.rpow_le_one (inv_nonneg.2 hA0.le) (inv_le_one_of_one_le₀ hA1) (by norm_num)
  have h58 := eq58 X hκ hE hB hs0 hst ht1 hc h.scaling hn (h.lift n hn)
  exact stochDom_of_indicator
    (Ωs := fun N (p : TimeIcc s t N × LoopData (B.L N) n) => gEv X E N p.1)
    (ξ := fun N (p : TimeIcc s t N × LoopData (B.L N) n) ω => ‖X.Lval E N p.1 ω p.2.idx‖)
    (ζ := aprioriRhs B E s t n) hΩ h58

/-- **Step 1 of Theorem 2.21**: under the hypotheses of Theorem 2.21 at the time `s` ((2.68),
(2.70), i.e. `RBM.BoundsCore`), (2.72), the regime `W ℓ_t η_t ≥ N^c`, and the random-layer
inputs `Hyp`, both conclusions (2.73) and (2.74) hold, in the shapes of the fields `apriori`
and `weakLaw` of `RBM.Steps`. -/
theorem step1 {κ : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) (hB : BoundsCore X E s)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hc : Cond272 B E s t)
    {c : ℝ} (hc0 : 0 < c) (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ B.scale E N (t N))
    (h : Hyp X E s t) :
    (∀ n : ℕ, 1 ≤ n → StochDom B.P
      (fun N (p : TimeIcc s t N × LoopData (B.L N) n) ω => ‖X.Lval E N p.1 ω p.2.idx‖)
      (fun N p _ => (B.ell N p.1 / B.ell N (s N)) ^ (n - 1) * (B.scale E N p.1)⁻¹ ^ (n - 1))) ∧
    StochDom B.P
      (fun N (p : TimeIcc s t N × (B.Idx N × B.Idx N)) ω => X.llErr E N p.1 ω p.2)
      (fun N p _ => (B.scale E N p.1)⁻¹ ^ ((1 : ℝ) / 4)) :=
  ⟨apriori X hκ hE hB hs0 hst ht1 hc hc0 hreg h, weakLaw X hκ hE hB hs0 hst ht1 hc hc0 hreg h⟩

end Main

end Step1

end RBM
