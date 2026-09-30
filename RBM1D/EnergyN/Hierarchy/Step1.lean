/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.Step1
import RBM1D.Flow.EnergyUniform
import RBM1D.Flow.Scales
import RBM1D.EnergyN.Loop.ContinuityAssembly
import RBM1D.EnergyN.Flow.Iteration

/-!
# Step 1 of the proof of Theorem 2.21 at an `N`-dependent energy

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, §5.1.

The statements of Step 1 ((5.2)–(5.9), leading to (2.73) and (2.74)) at an `N`-dependent energy
`E : ℕ → ℝ`.

## The external `κ`

`eq52_halfN` and `eq58_seqN` need a bound on `(2 / (mE (E N)).im)^n` that does not depend on
`N`. They take an explicit `κ` with `|E N| ≤ 2 - κ` (internally `κ' := min κ 1` for
`eq52_halfN`), derive the uniform bound `mκ := √(2κ')/2 ≤ (mE (E N)).im` for every `N`
(`mE_im_ge`), and use the constant `(2 / mκ)^n`; the pointwise inequality
`(2/(mE (E N)).im)^n ≤ (2/mκ)^n` gives the bound at each `N`. `eq55N`, `eq58N`, `weakLawN` and
`aprioriN` use this bound through `eq52_halfN` and `eq54N`; their `κ` hypothesis is needed for
`eq54N`'s use of the uniform constant of `stochDom_norm_Lval_of_LmKN`.

## Predicates

* `RBM.Step1.Lemma41FlowN` — Lemma 4.1 along the flow, as a hypothesis. It fixes no
  energy-dependent constant: the two quantities it threads, `goodEv`/`llMax`, carry no fixed
  constant.
* `RBM.Step1.HypN` — the hypotheses of Step 1, with fields `scaling : LoopScalingN …`
  (`RBM1D/EnergyN/Loop/ContinuityAssembly.lean`), `lift : NetLift …` (`NetLift` has no
  `E`-parameter of its own), `lemma41 : Lemma41FlowN …`, `cont : HighProb …`.
-/

namespace RBM

namespace Step1

open MeasureTheory Filter

section Generic

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℕ → ℝ} {s t : ℕ → ℝ}

/-- Under the step condition (2.72), eventually `1 ≤ W ℓ_s η_s` at the start time `s`. No
energy-dependent constant is fixed here. -/
theorem eventually_one_le_scale_sN (hE : ∀ N, |E N| < 2) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : Cond272N B E s t) :
    ∀ᶠ N : ℕ in atTop, 1 ≤ B.scale (E N) N (s N) := by
  filter_upwards [hc] with N hN
  exact (Step3.scale_facts_of_cond272 (by exact_mod_cast B.W_pos N) (B.one_le_L N) (hE N) le_rfl
    (hst N) (ht1 N) hN).1

/-- **(5.4)**: `|L_{s,σ,a}| ≺ (W ℓ_s η_s)^{-n+1}` at the start time `s`, from (2.68) and
(2.59). No energy-dependent constant is fixed here itself (it uses the uniform constant of
`stochDom_norm_Lval_of_LmKN`). -/
theorem eq54N {κ : ℝ} (hκ : 0 < κ) (hE : ∀ N, |E N| ≤ 2 - κ) (hB : BoundsCoreN X E s)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hc : Cond272N B E s t)
    {n : ℕ} (hn : 1 ≤ n) :
    StochDom B.P (fun N (v : LoopData (B.L N) n) ω => ‖X.Lval (E N) N (s N) ω v.idx‖)
      (fun N _ _ => (B.scale (E N) N (s N))⁻¹ ^ (n - 1)) := by
  have hE2 : ∀ N, |E N| < 2 := fun N => by linarith [hE N]
  have hk0 : 0 < min κ 1 := lt_min hκ one_pos
  have hEk : ∀ N, |E N| ≤ 2 - min κ 1 := fun N => (hE N).trans (by linarith [min_le_left κ 1])
  exact stochDom_norm_Lval_of_LmKN X hk0 (min_le_right κ 1) hEk (fun N => (hs0 N))
    (fun N => (hst N).trans_lt (ht1 N)) (eventually_one_le_scale_sN hE2 hst ht1 hc) hn
    (hB.LmK n hn)

/-- **(5.2) at time `1/2`**: `|L_{1/2,σ,a}| ≺ (W ℓ η)^{-n+1}`. The constant `(2/(mE (E N)).im)^n`
is bounded by the uniform `(2/mκ)^n`, `mκ := √(2κ)/2 ≤ (mE (E N)).im` for every `N`
(`mE_im_ge`). -/
theorem eq52_halfN {κ : ℝ} (hκ0 : 0 < κ) (hE : ∀ N, |E N| ≤ 2 - κ) {n : ℕ} (hn : 1 ≤ n) :
    StochDom B.P (fun N (v : LoopData (B.L N) n) ω => ‖X.Lval (E N) N (1 / 2) ω v.idx‖)
      (fun N _ _ => (B.scale (E N) N (1 / 2))⁻¹ ^ (n - 1)) := by
  have hE2 : ∀ N, |E N| < 2 := fun N => by linarith [hE N]
  set κ' : ℝ := min κ 1 with hκ'def
  have hκ'0 : 0 < κ' := lt_min hκ0 one_pos
  have hκ'1 : κ' ≤ 1 := min_le_right _ _
  have hκ'2 : κ' ≤ 2 := hκ'1.trans (by norm_num)
  have hEκ' : ∀ N, |E N| ≤ 2 - κ' := fun N => (hE N).trans (by linarith [min_le_left κ 1])
  have hm : ∀ N, Real.sqrt (2 * κ') / 2 ≤ (mE (E N)).im := fun N => mE_im_ge hκ'0 hκ'2 (hEκ' N)
  have hmpos : 0 < Real.sqrt (2 * κ') / 2 := by positivity
  refine stochDom_of_le_const_mul (fun _ _ _ => norm_nonneg _)
    (fun N _ _ => pow_nonneg (inv_nonneg.2 (B.scale_nonneg (E N) N (by norm_num))) _)
    ((2 / (Real.sqrt (2 * κ') / 2)) ^ n)
    (fun N v ω => ?_)
  have hbound : (2 / (mE (E N)).im) ^ n ≤ (2 / (Real.sqrt (2 * κ') / 2)) ^ n := by
    have h1 : (2 : ℝ) / (mE (E N)).im ≤ 2 / (Real.sqrt (2 * κ') / 2) :=
      div_le_div_of_nonneg_left (by norm_num) hmpos (hm N)
    exact pow_le_pow_left₀ (div_nonneg (by norm_num) (hmpos.trans_le (hm N)).le) h1 n
  refine (norm_Lval_le_of_le_half X (hE2 N) N (by norm_num) le_rfl ω hn v).trans ?_
  exact mul_le_mul_of_nonneg_right hbound
    (pow_nonneg (inv_nonneg.2 (B.scale_nonneg (E N) N (by norm_num))) _)

/-- **(5.5) at the start time**: for every `n ≥ 1`, `|L| ≺ (W ℓ η)^{-n+1}` at `startTime s`, from
(5.2) and (5.4). No energy-dependent constant is fixed here itself (it consumes the κ-bound
through `eq52_halfN`). -/
theorem eq55N {κ : ℝ} (hκ : 0 < κ) (hE : ∀ N, |E N| ≤ 2 - κ) (hB : BoundsCoreN X E s)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hc : Cond272N B E s t) :
    ∀ n : ℕ, 1 ≤ n → StochDom B.P
      (fun N (v : LoopData (B.L N) n) ω => ‖X.Lval (E N) N (startTime s N) ω v.idx‖)
      (fun N _ _ => (B.scale (E N) N (startTime s N))⁻¹ ^ (n - 1)) := by
  intro n hn
  refine stochDom_of_forall_or (eq54N X hκ hE hB hs0 hst ht1 hc hn) (eq52_halfN X hκ hE hn)
    fun N v ω => ?_
  rcases le_total (1 / 2) (s N) with h | h
  · left
    simp only [startTime, max_eq_left h, le_refl, and_self]
  · right
    simp only [startTime, max_eq_right h, le_refl, and_self]

/-- **(5.8) along a sequence of times `u N ∈ [s N, t N]`**:
`1(‖G_u‖_max ≤ 2) |L_{u,σ,a}| ≺ (ℓ_u/ℓ_s)^{n-1} (W ℓ_u η_u)^{-n+1}`. The constant
`(2/(mE (E N)).im)^n` is bounded by `(2/mκ)^n`, as in `eq52_halfN`. -/
theorem eq58_seqN {κ : ℝ} (hκ : 0 < κ) (hE : ∀ N, |E N| ≤ 2 - κ) (hB : BoundsCoreN X E s)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hc : Cond272N B E s t)
    (hS : ∀ t₁ t₂ : ℕ → ℝ, (∀ N, 1 / 2 ≤ t₁ N) → (∀ N, t₁ N ≤ t₂ N) → (∀ N, t₂ N < 1) →
      LoopScalingN X E t₁ t₂)
    (u : ∀ N, TimeIcc s t N) {n : ℕ} (hn : 1 ≤ n) :
    StochDom B.P (fun N (v : LoopData (B.L N) n) ω =>
        (gEv X (E N) N (u N)).indicator (fun ω => ‖X.Lval (E N) N (u N) ω v.idx‖) ω)
      (fun N _ _ => (B.ell N (u N) / B.ell N (s N)) ^ (n - 1) *
        (B.scale (E N) N (u N))⁻¹ ^ (n - 1)) := by
  have hE2 : ∀ N, |E N| < 2 := fun N => by linarith [hE N]
  have h1 : ∀ N, 1 / 2 ≤ startTime s N := fun N => le_max_right _ _
  have h12 : ∀ N, startTime s N ≤ max (u N : ℝ) (startTime s N) := fun N => le_max_right _ _
  have h2 : ∀ N, max (u N : ℝ) (startTime s N) < 1 := fun N =>
    max_lt ((u N).2.2.trans_lt (ht1 N)) (max_lt ((hst N).trans_lt (ht1 N)) (by norm_num))
  have h51 := lemma_5_1'N X hκ hE (c := 1 / 2) (by norm_num) h1 h12 h2
    (hS _ _ h1 h12 h2) (eq55N X hκ hE hB hs0 hst ht1 hc) n hn
  set κ' : ℝ := min κ 1 with hκ'def
  have hκ'0 : 0 < κ' := lt_min hκ one_pos
  have hκ'1 : κ' ≤ 1 := min_le_right _ _
  have hκ'2 : κ' ≤ 2 := hκ'1.trans (by norm_num)
  have hEκ' : ∀ N, |E N| ≤ 2 - κ' := fun N => (hE N).trans (by linarith [min_le_left κ 1])
  have hm : ∀ N, Real.sqrt (2 * κ') / 2 ≤ (mE (E N)).im := fun N => mE_im_ge hκ'0 hκ'2 (hEκ' N)
  have hmpos : 0 < Real.sqrt (2 * κ') / 2 := by positivity
  set C : ℝ := (2 / (Real.sqrt (2 * κ') / 2)) ^ n with hC
  have hC0 : 0 ≤ C := by positivity
  have hu0 : ∀ N, (0 : ℝ) ≤ (u N : ℝ) := fun N => (hs0 N).trans (u N).2.1
  have hu1 : ∀ N, (u N : ℝ) < 1 := fun N => (u N).2.2.trans_lt (ht1 N)
  have hζ0 : ∀ N, 0 ≤ (B.ell N (u N) / B.ell N (s N)) ^ (n - 1) *
      (B.scale (E N) N (u N))⁻¹ ^ (n - 1) := fun N => by
    have h := one_le_ell_div (B := B) (N := N) (u N).2.1 (hu1 N)
    have := (B.scale_pos' (hE2 N) N (hu0 N) (hu1 N))
    positivity
  have hdet : StochDom B.P
      (fun N (_ : LoopData (B.L N) n) (_ : Ω) => C * ((B.ell N (u N) / B.ell N (s N)) ^ (n - 1) *
        (B.scale (E N) N (u N))⁻¹ ^ (n - 1)))
      (fun N _ _ => (B.ell N (u N) / B.ell N (s N)) ^ (n - 1) *
        (B.scale (E N) N (u N))⁻¹ ^ (n - 1)) :=
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
    have hA := (B.scale_pos' (hE2 N) N (hu0 N) (hu1 N))
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
    have hind : (gEv X (E N) N (u N)).indicator (fun ω => ‖X.Lval (E N) N (u N) ω v.idx‖) ω ≤
        ‖X.Lval (E N) N (u N) ω v.idx‖ := Set.indicator_le_self' (fun _ _ => norm_nonneg _) ω
    refine hind.trans ((norm_Lval_le_of_le_half X (hE2 N) N (hu0 N) hhalf ω hn v).trans ?_)
    have hbound : (2 / (mE (E N)).im) ^ n ≤ C := by
      rw [hC]
      have h1 : (2 : ℝ) / (mE (E N)).im ≤ 2 / (Real.sqrt (2 * κ') / 2) :=
        div_le_div_of_nonneg_left (by norm_num) hmpos (hm N)
      exact pow_le_pow_left₀ (div_nonneg (by norm_num) (hmpos.trans_le (hm N)).le) h1 n
    have hR := one_le_pow₀ (n := n - 1) (one_le_ell_div (B := B) (N := N) (u N).2.1 (hu1 N))
    have hA := (B.scale_pos' (hE2 N) N (hu0 N) (hu1 N))
    have hA' : 0 ≤ (B.scale (E N) N (u N))⁻¹ ^ (n - 1) := by positivity
    have h2 := mul_le_mul_of_nonneg_right hR hA'
    rw [one_mul] at h2
    calc (2 / (mE (E N)).im) ^ n * (B.scale (E N) N (u N))⁻¹ ^ (n - 1)
        ≤ C * (B.scale (E N) N (u N))⁻¹ ^ (n - 1) := mul_le_mul_of_nonneg_right hbound hA'
      _ ≤ C * ((B.ell N (u N) / B.ell N (s N)) ^ (n - 1) *
          (B.scale (E N) N (u N))⁻¹ ^ (n - 1)) := mul_le_mul_of_nonneg_left h2 hC0

/-- **(5.8) uniformly in `u ∈ [s, t]`**, from `eq58_seqN` and the net lift `hlift`. No
energy-dependent constant is fixed here itself (it consumes the κ-bound through `eq58_seqN`). -/
theorem eq58N {κ : ℝ} (hκ : 0 < κ) (hE : ∀ N, |E N| ≤ 2 - κ) (hB : BoundsCoreN X E s)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hc : Cond272N B E s t)
    (hS : ∀ t₁ t₂ : ℕ → ℝ, (∀ N, 1 / 2 ≤ t₁ N) → (∀ N, t₁ N ≤ t₂ N) → (∀ N, t₂ N < 1) →
      LoopScalingN X E t₁ t₂)
    {n : ℕ} (hn : 1 ≤ n)
    (hlift : NetLift B.P s t
      (fun N (p : TimeIcc s t N × LoopData (B.L N) n) ω =>
        (gEv X (E N) N p.1).indicator (fun ω => ‖X.Lval (E N) N p.1 ω p.2.idx‖) ω)
      (fun N p _ => (B.ell N p.1 / B.ell N (s N)) ^ (n - 1) * (B.scale (E N) N p.1)⁻¹ ^ (n - 1))) :
    StochDom B.P
      (fun N (p : TimeIcc s t N × LoopData (B.L N) n) ω =>
        (gEv X (E N) N p.1).indicator (fun ω => ‖X.Lval (E N) N p.1 ω p.2.idx‖) ω)
      (fun N p _ => (B.ell N p.1 / B.ell N (s N)) ^ (n - 1) * (B.scale (E N) N p.1)⁻¹ ^ (n - 1)) :=
  hlift fun u => eq58_seqN X hκ hE hB hs0 hst ht1 hc hS u hn

/-- Under (2.72) and `N^c ≤ W ℓ_t η_t` eventually: eventually, for all `u ∈ [s, t]`,
`N^c ≤ W ℓ_u η_u` and `(ℓ_u/ℓ_s)^2 ≤ (W ℓ_u η_u)^{1/4}`. No energy-dependent constant is fixed
here. -/
theorem eventually_scale_factsN (hE : ∀ N, |E N| < 2) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : Cond272N B E s t) {c : ℝ}
    (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ B.scale (E N) N (t N)) :
    ∀ᶠ N : ℕ in atTop, ∀ u : TimeIcc s t N, (N : ℝ) ^ c ≤ B.scale (E N) N u ∧
      (B.ell N u / B.ell N (s N)) ^ 2 ≤ B.scale (E N) N u ^ ((1 : ℝ) / 4) := by
  filter_upwards [hc, hreg] with N hN hN'
  intro u
  have hW : (0 : ℝ) < B.W N := by exact_mod_cast B.W_pos N
  have hL := B.one_le_L N
  have hu1 : (u : ℝ) < 1 := u.2.2.trans_lt (ht1 N)
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  obtain ⟨hAs1, hAus, -, hkey⟩ :=
    Step3.scale_facts_of_cond272 hW hL (hE N) u.2.1 u.2.2 (ht1 N) hN
  have hanti := flowScale_antitoneOn hW.le (B.L N) (E N) (Set.mem_Iic.2 hu1.le)
    (Set.mem_Iic.2 (ht1 N).le) u.2.2
  refine ⟨hN'.trans hanti, ?_⟩
  change flowScale (B.W N) (B.L N) (E N) u ≤ flowScale (B.W N) (B.L N) (E N) (s N) at hAus
  set Au := flowScale (B.W N) (B.L N) (E N) u
  set As := flowScale (B.W N) (B.L N) (E N) (s N)
  have hAu : 0 < Au := flowScale_pos hW hL (hE N) hu1
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

/-- **Lemma 4.1 along the flow, as a hypothesis**: every bound `Φ` on the `(+,-)` 2-loops on the
event `goodEv` gives `llMax² ≺ Φ + W⁻¹` on that event. No energy-dependent constant is fixed here
(only the events `goodEv`/`llMax` are threaded through). -/
def Lemma41FlowN (X : Sample B) (E : ℕ → ℝ) (s t : ℕ → ℝ) : Prop :=
  ∀ Φ : ∀ N, TimeIcc s t N → ℝ, (∀ N u, 0 ≤ Φ N u) →
    StochDom B.P (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
        (goodEv X (E N) N p.1).indicator
          (fun ω => ‖X.Lval (E N) N p.1 ω (pmLoop p.2.1 p.2.2)‖) ω) (fun N p _ => Φ N p.1) →
    StochDom B.P (fun N (u : TimeIcc s t N) ω =>
        (goodEv X (E N) N u).indicator (fun ω => llMax X (E N) N u ω ^ 2) ω)
      (fun N u _ => Φ N u + (B.W N : ℝ)⁻¹)

/-- **The hypotheses of Step 1**: the loop scaling (6.1) on every `[t₁, t₂] ⊆ [1/2, 1)`, the net
lift of (5.8), Lemma 4.1 along the flow, and, with high probability, continuity of
`u ↦ llMax` on `[s, t]`. -/
structure HypN (X : Sample B) (E : ℕ → ℝ) (s t : ℕ → ℝ) : Prop where
  scaling : ∀ t₁ t₂ : ℕ → ℝ, (∀ N, 1 / 2 ≤ t₁ N) → (∀ N, t₁ N ≤ t₂ N) → (∀ N, t₂ N < 1) →
    LoopScalingN X E t₁ t₂
  lift : ∀ n : ℕ, 1 ≤ n → NetLift B.P s t
    (fun N (p : TimeIcc s t N × LoopData (B.L N) n) ω =>
      (gEv X (E N) N p.1).indicator (fun ω => ‖X.Lval (E N) N p.1 ω p.2.idx‖) ω)
    (fun N p _ => (B.ell N p.1 / B.ell N (s N)) ^ (n - 1) * (B.scale (E N) N p.1)⁻¹ ^ (n - 1))
  lemma41 : Lemma41FlowN X E s t
  cont : HighProb B.P
    (fun N => {ω | ContinuousOn (fun u => llMax X (E N) N u ω) (Set.Icc (s N) (t N))})

/-- **The forbidden-region argument (5.9)**: from (5.8) for `n = 2`, Lemma 4.1 along the flow and
continuity, with high probability `llMax < (W ℓ_u η_u)^{-1/4}` for all `u ∈ [s, t]`. No
energy-dependent constant is fixed here (it receives `h58` already proved). -/
theorem weakLaw_highProbN (hE : ∀ N, |E N| < 2) (hB : BoundsCoreN X E s) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hc : Cond272N B E s t) {c : ℝ} (hc0 : 0 < c)
    (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ B.scale (E N) N (t N))
    (h58 : StochDom B.P
      (fun N (p : TimeIcc s t N × LoopData (B.L N) 2) ω =>
        (gEv X (E N) N p.1).indicator (fun ω => ‖X.Lval (E N) N p.1 ω p.2.idx‖) ω)
      (fun N p _ => (B.ell N p.1 / B.ell N (s N)) ^ (2 - 1) * (B.scale (E N) N p.1)⁻¹ ^ (2 - 1)))
    (h41 : Lemma41FlowN X E s t)
    (hcont : HighProb B.P
      (fun N => {ω | ContinuousOn (fun u => llMax X (E N) N u ω) (Set.Icc (s N) (t N))})) :
    HighProb B.P (fun N => {ω | ∀ u : TimeIcc s t N,
      llMax X (E N) N u ω < (B.scale (E N) N u)⁻¹ ^ ((1 : ℝ) / 4)}) := by
  have hu0 : ∀ N (u : TimeIcc s t N), (0 : ℝ) ≤ (u : ℝ) := fun N u => (hs0 N).trans u.2.1
  have hu1 : ∀ N (u : TimeIcc s t N), (u : ℝ) < 1 := fun N u => u.2.2.trans_lt (ht1 N)
  have hA : ∀ N (u : TimeIcc s t N), 0 < B.scale (E N) N u := fun N u =>
    B.scale_pos' (hE N) N (hu0 N u) (hu1 N u)
  have hfacts := eventually_scale_factsN hE hst ht1 hc hreg
  -- `A_u ≥ 1` for large `N`
  have hA1 : ∀ᶠ N : ℕ in atTop, ∀ u : TimeIcc s t N, 1 ≤ B.scale (E N) N u := by
    filter_upwards [hfacts, eventually_ge_atTop 1] with N hN hN1 u
    exact (Real.one_le_rpow (by exact_mod_cast hN1) hc0.le).trans (hN u).1
  -- `q = N^{c/8} ≥ 2` for large `N`
  have hq2 : ∀ᶠ N : ℕ in atTop, (2 : ℝ) ≤ (N : ℝ) ^ (c / 8) :=
    eventually_le_rpow 2 (by positivity)
  set Φ : ∀ N, TimeIcc s t N → ℝ := fun N u =>
    B.ell N u / B.ell N (s N) * (B.scale (E N) N u)⁻¹ with hΦdef
  have hΦ0 : ∀ N u, 0 ≤ Φ N u := fun N u => by
    have h := one_le_ell_div (B := B) (N := N) u.2.1 (hu1 N u)
    have := hA N u
    simp only [hΦdef]; positivity
  -- (5.8) at `n = 2`, for `σ = (+,-)`
  have h2 := h58.precomp_param
    (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) => (p.1, Step45.pmData p.2.1 p.2.2))
  simp only [Step45.pmData_idx, Nat.reduceSub, pow_one] at h2
  -- the input of Lemma 4.1, on its good event
  have hin : StochDom B.P
      (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
        (goodEv X (E N) N p.1).indicator
          (fun ω => ‖X.Lval (E N) N p.1 ω (pmLoop p.2.1 p.2.2)‖) ω)
      (fun N p _ => Φ N p.1) := by
    refine stochDom_of_le_left_eventually ?_ h2
    filter_upwards [hA1] with N hN p ω
    exact Set.indicator_le_indicator_of_subset (goodEv_subset_gEv X (hE N).le (hN p.1))
      (fun _ => norm_nonneg _) ω
  -- Lemma 4.1, then square roots
  have hM2 := h41 Φ hΦ0 hin
  have hM := StochDom.sqrt_of
    (fun N (u : TimeIcc s t N) ω =>
      Set.indicator_nonneg (fun ω _ => sq_nonneg (llMax X (E N) N u ω)) ω)
    (fun N (u : TimeIcc s t N) _ => add_nonneg (hΦ0 N u) (inv_nonneg.2 (Nat.cast_nonneg _))) hM2
  have hM' : StochDom B.P
      (fun N (u : TimeIcc s t N) ω => {ω | llMax X (E N) N u ω ≤
        (B.scale (E N) N u)⁻¹ ^ ((1 : ℝ) / 6)}.indicator (fun ω => llMax X (E N) N u ω) ω)
      (fun N u _ => Real.sqrt (Φ N u + (B.W N : ℝ)⁻¹)) := by
    refine StochDom.of_le_left (fun N u ω => le_of_eq ?_) hM
    by_cases hω : ω ∈ goodEv X (E N) N u
    · have hω' : ω ∈ {ω | llMax X (E N) N u ω ≤ (B.scale (E N) N u)⁻¹ ^ ((1 : ℝ) / 6)} := hω
      rw [Set.indicator_of_mem hω', Set.indicator_of_mem hω,
        Real.sqrt_sq (llMax_nonneg X N u ω)]
    · have hω' : ω ∉ {ω | llMax X (E N) N u ω ≤ (B.scale (E N) N u)⁻¹ ^ ((1 : ℝ) / 6)} := hω
      rw [Set.indicator_of_notMem hω', Set.indicator_of_notMem hω, Real.sqrt_zero]
  -- the forbidden region (5.9)
  have hforb := forbidden_region (P := B.P)
    (a := fun N (u : TimeIcc s t N) => (B.scale (E N) N u)⁻¹ ^ ((1 : ℝ) / 4))
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
        (inv_W_le_inv_scale (hE N) N (hu0 N u) (hu1 N u)))
    hM'
  -- the initial condition at `u = s`, from (2.70)
  have hinit : HighProb B.P (fun N => {ω | llMax X (E N) N (s N) ω <
      (B.scale (E N) N (s N))⁻¹ ^ ((1 : ℝ) / 4)}) := by
    refine (hB.localLaw.highProb (by positivity : 0 < c / 8)).mono ?_
    filter_upwards [hfacts, hq2] with N hN hq ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    have hAs := hA N ⟨s N, le_rfl, hst N⟩
    have h1 := rpow_eighth_le (hN ⟨s N, le_rfl, hst N⟩).1
    exact (llMax_le X hω).trans_lt (init_arith hAs hq h1)
  -- continuity of `a(u) = (W ℓ_u η_u)^{-1/4}`
  have hacont : ∀ N, ContinuousOn (fun u => (B.scale (E N) N u)⁻¹ ^ ((1 : ℝ) / 4))
      (Set.Icc (s N) (t N)) := fun N =>
    ((continuousOn_scale N (ht1 N)).inv₀ fun u hu =>
      (B.scale_pos' (hE N) N ((hs0 N).trans hu.1) (hu.2.trans_lt (ht1 N))).ne').rpow_const
      fun _ _ => Or.inr (by norm_num)
  -- `a ≤ b`
  have hab : ∀ᶠ N : ℕ in atTop, ∀ u : TimeIcc s t N,
      (B.scale (E N) N u)⁻¹ ^ ((1 : ℝ) / 4) ≤ (B.scale (E N) N u)⁻¹ ^ ((1 : ℝ) / 6) := by
    filter_upwards [hA1] with N hN u
    exact Real.rpow_le_rpow_of_exponent_ge (inv_pos.2 (hA N u)) (inv_le_one_of_one_le₀ (hN u))
      (by norm_num)
  exact bootstrap (M := fun N u ω => llMax X (E N) N u ω)
    (a := fun N u => (B.scale (E N) N u)⁻¹ ^ ((1 : ℝ) / 4))
    (b := fun N u => (B.scale (E N) N u)⁻¹ ^ ((1 : ℝ) / 6)) hcont hacont hab hforb hinit

/-- **(2.74)**: `‖G_u - m‖_max ≺ (W ℓ_u η_u)^{-1/4}`, uniformly in `u ∈ [s, t]`. -/
theorem weakLawN {κ : ℝ} (hκ : 0 < κ) (hE : ∀ N, |E N| ≤ 2 - κ) (hB : BoundsCoreN X E s)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hc : Cond272N B E s t)
    {c : ℝ} (hc0 : 0 < c) (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ B.scale (E N) N (t N))
    (h : HypN X E s t) :
    StochDom B.P
      (fun N (p : TimeIcc s t N × (B.Idx N × B.Idx N)) ω => X.llErr (E N) N p.1 ω p.2)
      (fun N p _ => (B.scale (E N) N p.1)⁻¹ ^ ((1 : ℝ) / 4)) := by
  have hE2 : ∀ N, |E N| < 2 := fun N => by linarith [hE N]
  have hw := weakLaw_highProbN X hE2 hB hs0 hst ht1 hc hc0 hreg
    (eq58N X hκ hE hB hs0 hst ht1 hc h.scaling (by norm_num) (h.lift 2 (by norm_num)))
    h.lemma41 h.cont
  refine stochDom_of_highProb (fun N p _ => Real.rpow_nonneg (inv_nonneg.2
    (B.scale_nonneg (E N) N (p.1.2.2.trans (ht1 N).le))) _) ?_
  refine hw.mono (Eventually.of_forall fun N ω hω p => ?_)
  simp only [Set.mem_ofPred_eq] at hω ⊢
  exact (llErr_le_llMax X N p.1 ω p.2).trans (hω p.1).le

/-- **(2.73)**: `|L_{u,σ,a}| ≺ (ℓ_u/ℓ_s)^{n-1} (W ℓ_u η_u)^{-n+1}`, uniformly in `u ∈ [s, t]`, for
every `n ≥ 1`. -/
theorem aprioriN {κ : ℝ} (hκ : 0 < κ) (hE : ∀ N, |E N| ≤ 2 - κ) (hB : BoundsCoreN X E s)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hc : Cond272N B E s t)
    {c : ℝ} (hc0 : 0 < c) (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ B.scale (E N) N (t N))
    (h : HypN X E s t) :
    ∀ n : ℕ, 1 ≤ n → StochDom B.P
      (fun N (p : TimeIcc s t N × LoopData (B.L N) n) ω => ‖X.Lval (E N) N p.1 ω p.2.idx‖)
      (fun N p _ => (B.ell N p.1 / B.ell N (s N)) ^ (n - 1) *
        (B.scale (E N) N p.1)⁻¹ ^ (n - 1)) := by
  intro n hn
  have hE2 : ∀ N, |E N| < 2 := fun N => by linarith [hE N]
  have hw := weakLaw_highProbN X hE2 hB hs0 hst ht1 hc hc0 hreg
    (eq58N X hκ hE hB hs0 hst ht1 hc h.scaling (by norm_num) (h.lift 2 (by norm_num)))
    h.lemma41 h.cont
  have hfacts := eventually_scale_factsN hE2 hst ht1 hc hreg
  have hΩ : HighProb B.P (fun N => {ω | ∀ p : TimeIcc s t N × LoopData (B.L N) n,
      ω ∈ gEv X (E N) N p.1}) := by
    refine hw.mono ?_
    filter_upwards [hfacts, eventually_ge_atTop 1] with N hN hN1 ω hω p
    simp only [Set.mem_ofPred_eq] at hω ⊢
    have hA1 : 1 ≤ B.scale (E N) N p.1 :=
      (Real.one_le_rpow (by exact_mod_cast hN1) hc0.le).trans (hN p.1).1
    have hA0 : 0 < B.scale (E N) N p.1 := by linarith
    refine mem_gEv_of_llMax_le_one X (hE2 N).le ((hω p.1).le.trans ?_)
    exact Real.rpow_le_one (inv_nonneg.2 hA0.le) (inv_le_one_of_one_le₀ hA1) (by norm_num)
  have h58 := eq58N X hκ hE hB hs0 hst ht1 hc h.scaling hn (h.lift n hn)
  exact stochDom_of_indicator
    (Ωs := fun N (p : TimeIcc s t N × LoopData (B.L N) n) => gEv X (E N) N p.1)
    (ξ := fun N (p : TimeIcc s t N × LoopData (B.L N) n) ω => ‖X.Lval (E N) N p.1 ω p.2.idx‖)
    (ζ := fun N p _ => (B.ell N p.1 / B.ell N (s N)) ^ (n - 1) * (B.scale (E N) N p.1)⁻¹ ^ (n - 1))
    hΩ h58

end Generic

end Step1

end RBM
