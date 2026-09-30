/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.Step45
import RBM1D.Loop.ContinuityAssembly
import RBM1D.Defs.StochDomHighProb
import RBM1D.Gauss.GoodSetFlowCore

/-!
# Step 1 of the proof of Theorem 2.21: (2.73) and (2.74)

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, §5.1: the a priori loop
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
* `startTime s = max(s, 1/2)` — the time `t₁` from which Lemma 5.1 is applied in (5.5), (5.8).
* `NetLift` (hypothesis predicate) — the continuity argument of §5.1 for the family of (5.8):
  bounds along every time sequence give bounds uniform in `u`; `loopInd` — the left side of
  (5.8).

The loop bounds (5.4), (5.5), (5.8), the weak law (5.9) and Step 1 itself, (2.73) and (2.74),
are proved from these at an `N`-dependent energy `E_N` in `RBM1D/EnergyN/Hierarchy/Step1.lean`
(`RBM.Step1.aprioriN`, `RBM.Step1.weakLawN`).

## Hypotheses (never axioms)

* (2.68), (2.70) at time `s` (the hypotheses of Theorem 2.21 that Step 1 uses; (2.69) and
  (2.71) are not used), (2.72), `|E| ≤ 2 - κ`, `0 < s ≤ t < 1`.
* The regime `W ℓ_t η_t ≥ N^c` for some `c > 0` (see Deviations).
* The random-layer inputs, bundled as `RBM.Step1.HypN`: (6.1), the input of Lemma 5.1, for
  `1/2 ≤ t₁ ≤ t₂ < 1`; the continuity argument of §5.1 ("`N^{-C}` net + (5.1)") for the family
  of (5.8), in the form `NetLift`; Lemma 4.1 (4.2)+(4.3) at the times `u ∈ [s,t]` on
  `{‖G_u - m‖_max ≤ (W ℓ_u η_u)^{-1/6}}`; and the time continuity behind (5.1): w.h.p.
  `u ↦ ‖G_u - m‖_max` is continuous on `[s, t]`.

## Deviations from the paper

* **Regime.** "`≪`" in (5.9) needs `W ℓ_u η_u ≥ N^c`, which Theorem 2.21 obtains from its
  hypothesis `t ≤ 1 - N^{-1+τ}`; here `W ℓ_t η_t ≥ N^c` is assumed directly, eventually (see
  `docs/PAPER-VS-LEAN.md` §5.2).  All three cases are also stated for time sequences
  `s(N), t(N)`, so the case split is made for each `N` (`startTime`).
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
  `Φ_u + W⁻¹` ((4.2) contributes `W⁻¹`); `W⁻¹ ≤ (W ℓ_u η_u)⁻¹` since `ℓ_u η_u ≤ 1`.
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

/-- **The continuity argument of §5.1 ("`N^{-C}` net + (5.1)"), as a hypothesis** on a
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

end WeakLaw

/-! ### Step 1: (2.73) and (2.74) -/

section Main

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}

end Main

end Step1

end RBM
