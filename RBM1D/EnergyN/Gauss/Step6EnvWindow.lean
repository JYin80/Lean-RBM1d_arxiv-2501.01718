/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Step6EnvWindow
import RBM1D.EnergyN.Hierarchy.Step6
import RBM1D.EnergyN.Gauss.Step6DriftSplit
import RBM1D.EnergyN.Unif.Flow.Iteration

/-!
# Step 6, the window theorems, drift half, at an `N`-dependent energy

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.8, (5.126)–(5.136), and §2.7, (2.71), (2.80).

Five statements of Step 6 at an `N`-dependent energy `E : ℕ → ℝ`: the bounds
`|driftELK| ≤ W ℓ (W ℓ η)^{-4}` (`RBM.unifDetDom_driftELK'N`) and
`|driftEG| ≤ W ℓ (W ℓ η)^{-4}` (`RBM.unifDetDom_driftEG'N`), the fast-decay hypothesis
(`RBM.fastDecayHyp_driftSplit'N`), the drift bound (`RBM.driftBound_driftEG'N`), and (2.80)
(`RBM.sharpExpect_step6_driftEG'N`).

## The external `κ`

`RBM.unifDetDom_driftEG'N` needs a kernel constant `CK` (`n = 3`) in the slot of
`SumZeroDyn.eventually_const_mul_rpow_le (12·e·(1+CK))`. It takes `CK` from
`RBM.Band.norm_Kval_le_unif` (`∃ C, 0 ≤ C ∧ ∀ E, |E| ≤ 2 - k → …`,
`EnergyN/Unif/Flow/Iteration.lean`), obtained once before `N` and instantiated at `E N` via
`hEκ N` at the one call site, as `Gauss.quad11_unifDetDom'N` does.

## The diagonal hypotheses of `sharpExpect_step6_driftEG'N`

`RBM.sharpExpect_step6_driftEG'N` uses `RBM.hierarchyN_driftSplit`, so it takes the hypotheses
`hcont`/`hintL2`/`hintQ`/`hintG`/`hEL`/`hintU1`/`hintU2` in the diagonal shape of
`RBM.hierarchyN_driftSplit`: an extra outer `∀ N₀` binder with `E N₀` in place of `E` throughout
(in addition to the inner `∀ N` of each hypothesis). This shape comes from the diagonal helper;
it is not an added mathematical hypothesis (at a constant energy sequence it is the fixed-`E`
shape).

## Main declarations

* `RBM.unifDetDom_driftELK'N`, `RBM.fastDecayHyp_driftSplit'N` — no energy-dependent constant.
* `RBM.unifDetDom_driftEG'N` — the kernel constant fixed as above.
* `RBM.driftBound_driftEG'N`, `RBM.sharpExpect_step6_driftEG'N` — built from the four above
  (and, for the last, `hierarchyN_driftSplit`).
-/

open MeasureTheory Filter

namespace RBM

section WindowN

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

open Real in
set_option maxHeartbeats 1000000 in
/-- **`|driftELK| ≤ W ℓ_u (W ℓ_u η_u)^{-4}`** (deterministic domination, `UnifDetDom`), from the
envelope `henv`, the lower bound `hlow` and the inputs `QuadInputs` with high probability. No
energy-dependent constant is fixed here: every crossing constant is `E`-free. -/
theorem unifDetDom_driftELK'N (X : Sample B) {E : ℕ → ℝ} {s t : ℕ → ℝ}
    (hE : ∀ N, |E N| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hc : Cond272N B E s t) {Env : ℕ → ℝ} {Kenv Blow : ℝ}
    (hmeas : ∀ (N : ℕ) (v : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2),
      AEStronglyMeasurable (fun ω => primBil (B.L N) (B.W N) (lkPath X (E N) N (v : ℝ) ω)
        (lkPath X (E N) N (v : ℝ) ω) (LoopData.idx (σ, a))) B.P)
    (henv : ∀ (N : ℕ) (v : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2) (ω : Ω),
      ‖primBil (B.L N) (B.W N) (lkPath X (E N) N (v : ℝ) ω) (lkPath X (E N) N (v : ℝ) ω)
        (LoopData.idx (σ, a))‖ ≤ Env N)
    (hEnv0 : ∀ N, 0 ≤ Env N)
    (hKenv : 0 ≤ Kenv) (hEnvpoly : ∀ᶠ N : ℕ in atTop, Env N ≤ (N : ℝ) ^ Kenv)
    (hB : 0 ≤ Blow)
    (hlow : ∀ᶠ N : ℕ in atTop, ∀ u : TimeIcc s t N, (N : ℝ) ^ (-Blow)
      ≤ (B.W N : ℝ) * B.ell N (u : ℝ) * (B.scale (E N) N (u : ℝ))⁻¹ ^ 4)
    (hin : ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), HighProb B.P (fun N =>
      QuadInputs X (E N) s t N ((N : ℝ) ^ τ) ((N : ℝ) ^ (-D)) ((N : ℝ) ^ τ))) :
    UnifDetDom (fun N (p : TimeIcc s t N × LoopData (B.L N) 2) =>
        ‖driftELK X (E N) N p.1 p.2.1 p.2.2‖)
      (fun N p => (B.W N : ℝ) * B.ell N p.1 * (B.scale (E N) N p.1)⁻¹ ^ 4) := by
  have hP := B.isProbabilityMeasure
  intro τ hτ
  set τ₁ : ℝ := τ / 8 with hτ₁def
  have hτ₁ : 0 < τ₁ := by rw [hτ₁def]; linarith
  set D₁ : ℝ := Blow + Kenv + τ₁ + 4 with hD₁def
  have hD₁ : 0 < D₁ := by rw [hD₁def]; linarith
  filter_upwards [hin τ₁ hτ₁ D₁ hD₁ D₁ hD₁,
    SumZeroDyn.flow_crudeN hE hs0 hst ht1 hc, hEnvpoly, hlow,
    SumZeroDyn.eventually_const_mul_rpow_le (24 * exp 1)
      (show 3 * τ₁ < τ / 2 by rw [hτ₁def]; linarith),
    SumZeroDyn.eventually_const_mul_rpow_le 4
      (show 2 + τ₁ - D₁ < -Blow - 1 by rw [hD₁def]; linarith),
    SumZeroDyn.eventually_const_mul_rpow_le 1
      (show Kenv - D₁ < -Blow - 1 by rw [hD₁def]; linarith),
    SumZeroDyn.eventually_const_mul_rpow_le 2 (show τ / 2 < τ by linarith),
    eventually_ge_atTop 2] with N hgood hcr hEnvN hlowN hmainN herr1N herr2N hfinN hN2
  obtain ⟨hLN, hWN, _, hu⟩ := hcr
  rintro ⟨v, q⟩
  have hN2' : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
  have hN1' : (1 : ℝ) ≤ (N : ℝ) := by linarith
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  set u : ℝ := (v : ℝ) with hudef
  have hu0 : 0 ≤ u := (hs0 N).trans v.2.1
  have hu1 : u < 1 := v.2.2.trans_lt (ht1 N)
  have hη : 0 < etaT (E N) u := etaT_pos (hE N) hu1
  have hA : 1 ≤ B.scale (E N) N u := (hu v).1
  have hA0 : (0 : ℝ) < B.scale (E N) N u := lt_of_lt_of_le zero_lt_one hA
  have hell : (1 : ℝ) / 2 ≤ B.ell N u := by
    have := one_le_ellHat (B.L N) (B.three_le_L N) hu0 hu1
    rw [Band.ell]; linarith
  set Gt : ℝ := (B.W N : ℝ) * B.ell N u * (B.scale (E N) N u)⁻¹ ^ 4 with hGtdef
  have hGt0 : 0 ≤ Gt := by
    have hW : (0 : ℝ) ≤ B.W N := Nat.cast_nonneg _
    have : (0 : ℝ) ≤ (B.scale (E N) N u)⁻¹ ^ 4 := by positivity
    have hℓ0 : (0 : ℝ) ≤ B.ell N u := by linarith
    rw [hGtdef]; positivity
  have hGtlow : (N : ℝ) ^ (-Blow) ≤ Gt := hlowN v
  set Krad : ℝ := (N : ℝ) ^ τ₁ with hKraddef
  set δ : ℝ := (N : ℝ) ^ (-D₁) with hδdef
  have hKrad1 : (1 : ℝ) ≤ Krad := Real.one_le_rpow hN1' hτ₁.le
  have hδ0 : (0 : ℝ) ≤ δ := Real.rpow_nonneg hN0.le _
  -- the pointwise bound on the good set
  set c : ℝ := 8 * exp 1 * (Krad + 2) * Krad ^ 2 * Gt + 4 * ((B.W N : ℝ) * (B.L N : ℝ) * δ) * Krad
    with hcdef
  have hc0 : 0 ≤ c := by
    have hW : (0 : ℝ) ≤ B.W N := Nat.cast_nonneg _
    have hL : (0 : ℝ) ≤ B.L N := Nat.cast_nonneg _
    have hK0 : (0 : ℝ) ≤ Krad := by linarith
    rw [hcdef]
    have h1 : (0 : ℝ) ≤ 8 * exp 1 * (Krad + 2) * Krad ^ 2 * Gt := by positivity
    have h2 : (0 : ℝ) ≤ 4 * ((B.W N : ℝ) * (B.L N : ℝ) * δ) * Krad := by positivity
    linarith
  have hpt : ∀ ω ∈ QuadInputs X (E N) s t N Krad δ Krad,
      ‖primBil (B.L N) (B.W N) (lkPath X (E N) N u ω) (lkPath X (E N) N u ω)
        (LoopData.idx (q.1, q.2))‖ ≤ c := by
    intro ω hω
    obtain ⟨hDd, hΨ⟩ := hω v
    have hxi0 : 0 ≤ X.xiLK (E N) N u ω 2 := X.xiLK_nonneg hA0.le
    have hbase := norm_primBil_lkPath_le X N ω q.1 q.2 (hE N) hu1 hA hell hKrad1 hδ0 hDd
    refine hbase.trans ?_
    rw [hcdef, ← hGtdef]
    have h1 : X.xiLK (E N) N u ω 2 ^ 2 ≤ Krad ^ 2 := by
      have : X.xiLK (E N) N u ω 2 ≤ Krad := hΨ
      nlinarith
    have hcoef : (0 : ℝ) ≤ 8 * exp 1 * (Krad + 2) := by
      have : (0 : ℝ) ≤ Krad := by linarith
      positivity
    have hWLd : (0 : ℝ) ≤ 4 * ((B.W N : ℝ) * (B.L N : ℝ) * δ) := by
      have hW : (0 : ℝ) ≤ B.W N := Nat.cast_nonneg _
      have hL : (0 : ℝ) ≤ B.L N := Nat.cast_nonneg _
      positivity
    have hA' : 8 * exp 1 * (Krad + 2) * X.xiLK (E N) N u ω 2 ^ 2 * Gt
        ≤ 8 * exp 1 * (Krad + 2) * Krad ^ 2 * Gt := by
      have := mul_le_mul_of_nonneg_left h1 hcoef
      exact mul_le_mul_of_nonneg_right this hGt0
    have hB' : 4 * ((B.W N : ℝ) * (B.L N : ℝ) * δ) * X.xiLK (E N) N u ω 2
        ≤ 4 * ((B.W N : ℝ) * (B.L N : ℝ) * δ) * Krad :=
      mul_le_mul_of_nonneg_left hΨ hWLd
    linarith
  -- the first moment
  have hbad : (B.P (QuadInputs X (E N) s t N Krad δ Krad)ᶜ).toReal ≤ δ :=
    ENNReal.toReal_le_of_le_ofReal hδ0 hgood
  have hstep : ‖driftELK X (E N) N v q.1 q.2‖ ≤ c + Env N * δ := by
    have := norm_integral_le_add_measure_compl (P := B.P)
      (f := fun ω => primBil (B.L N) (B.W N) (lkPath X (E N) N u ω) (lkPath X (E N) N u ω)
        (LoopData.idx (q.1, q.2)))
      (hmeas N v q.1 q.2) (G := QuadInputs X (E N) s t N Krad δ Krad) hc0 hpt
      (fun ω => henv N v q.1 q.2 ω)
    refine this.trans ?_
    have := mul_le_mul_of_nonneg_left hbad (hEnv0 N)
    linarith
  refine hstep.trans ?_
  -- the `Ξ`-bookkeeping: main term, two errors
  have hWL : (B.W N : ℝ) * (B.L N : ℝ) ≤ (N : ℝ) ^ (2 : ℝ) := by
    have h2 : (N : ℝ) ^ (2 : ℝ) = (N : ℝ) * (N : ℝ) := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
    have hW0 : (0 : ℝ) ≤ B.W N := Nat.cast_nonneg _
    have hL0 : (0 : ℝ) ≤ B.L N := Nat.cast_nonneg _
    rw [h2]; nlinarith
  have hmain : 8 * exp 1 * (Krad + 2) * Krad ^ 2 * Gt ≤ (N : ℝ) ^ (τ / 2) * Gt := by
    have h3 : Krad + 2 ≤ 3 * Krad := by linarith
    have hK0 : (0 : ℝ) ≤ Krad := by linarith
    have hstep2 : 8 * exp 1 * (Krad + 2) * Krad ^ 2 ≤ 24 * exp 1 * (N : ℝ) ^ (3 * τ₁) := by
      have hk3 : Krad ^ 3 = (N : ℝ) ^ (3 * τ₁) := by
        rw [hKraddef, ← Real.rpow_natCast ((N : ℝ) ^ τ₁) 3, ← Real.rpow_mul hN0.le]
        norm_num [mul_comm]
      have : 8 * exp 1 * (Krad + 2) * Krad ^ 2 ≤ 8 * exp 1 * (3 * Krad) * Krad ^ 2 := by
        have : (0 : ℝ) ≤ 8 * exp 1 * Krad ^ 2 := by positivity
        nlinarith [exp_nonneg (1 : ℝ)]
      calc 8 * exp 1 * (Krad + 2) * Krad ^ 2 ≤ 8 * exp 1 * (3 * Krad) * Krad ^ 2 := this
        _ = 24 * exp 1 * Krad ^ 3 := by ring
        _ = 24 * exp 1 * (N : ℝ) ^ (3 * τ₁) := by rw [hk3]
    exact mul_le_mul_of_nonneg_right (hstep2.trans hmainN) hGt0
  have herr1 : 4 * ((B.W N : ℝ) * (B.L N : ℝ) * δ) * Krad ≤ (N : ℝ) ^ (-Blow - 1) := by
    have he : (N : ℝ) ^ (2 : ℝ) * δ * Krad = (N : ℝ) ^ (2 + τ₁ - D₁) := by
      rw [hδdef, hKraddef, ← Real.rpow_add hN0, ← Real.rpow_add hN0]
      congr 1; ring
    have hmono : 4 * ((B.W N : ℝ) * (B.L N : ℝ) * δ) * Krad
        ≤ 4 * ((N : ℝ) ^ (2 : ℝ) * δ) * Krad := by
      have hK0 : (0 : ℝ) ≤ Krad := by linarith
      have : (B.W N : ℝ) * (B.L N : ℝ) * δ ≤ (N : ℝ) ^ (2 : ℝ) * δ :=
        mul_le_mul_of_nonneg_right hWL hδ0
      nlinarith
    refine hmono.trans ?_
    calc 4 * ((N : ℝ) ^ (2 : ℝ) * δ) * Krad = 4 * ((N : ℝ) ^ (2 : ℝ) * δ * Krad) := by ring
      _ = 4 * (N : ℝ) ^ (2 + τ₁ - D₁) := by rw [he]
      _ ≤ (N : ℝ) ^ (-Blow - 1) := herr1N
  have herr2 : Env N * δ ≤ (N : ℝ) ^ (-Blow - 1) := by
    have h1 : Env N * δ ≤ (N : ℝ) ^ Kenv * δ := mul_le_mul_of_nonneg_right hEnvN hδ0
    have he : (N : ℝ) ^ Kenv * δ = (N : ℝ) ^ (Kenv - D₁) := by
      rw [hδdef, ← Real.rpow_add hN0, sub_eq_add_neg]
    refine h1.trans ?_
    rw [he]
    calc (N : ℝ) ^ (Kenv - D₁) = 1 * (N : ℝ) ^ (Kenv - D₁) := by ring
      _ ≤ (N : ℝ) ^ (-Blow - 1) := herr2N
  have hsumerr : (N : ℝ) ^ (-Blow - 1) + (N : ℝ) ^ (-Blow - 1) ≤ Gt := by
    have hmul : (N : ℝ) ^ (-Blow - 1) * (N : ℝ) ^ (1 : ℝ) = (N : ℝ) ^ (-Blow) := by
      rw [← Real.rpow_add hN0]; congr 1; ring
    have hp : (0 : ℝ) ≤ (N : ℝ) ^ (-Blow - 1) := Real.rpow_nonneg hN0.le _
    have h2 : (N : ℝ) ^ (-Blow - 1) + (N : ℝ) ^ (-Blow - 1) ≤ (N : ℝ) ^ (-Blow) := by
      rw [← hmul, Real.rpow_one]
      nlinarith
    exact h2.trans hGtlow
  have hfin : (N : ℝ) ^ (τ / 2) * Gt + Gt ≤ (N : ℝ) ^ τ * Gt := by
    have h1 : (1 : ℝ) ≤ (N : ℝ) ^ (τ / 2) := Real.one_le_rpow hN1' (by linarith)
    have h2 : (N : ℝ) ^ (τ / 2) + 1 ≤ (N : ℝ) ^ τ := by
      have := hfinN
      linarith
    have := mul_le_mul_of_nonneg_right h2 hGt0
    linarith [this]
  rw [hcdef]
  linarith [hmain, herr1, herr2, hsumerr, hfin]

set_option maxHeartbeats 1000000 in
/-- **The fast-decay hypothesis `Step6.FastDecayHypN` for the drift tensors `driftELKN`,
`driftEGN`**, from the fast decay of `L - K` at `s` and the inputs `FDInputs`. No
energy-dependent constant is fixed here. -/
theorem fastDecayHyp_driftSplit'N (X : Sample B) {E : ℕ → ℝ} {s t : ℕ → ℝ}
    (hE : ∀ N, |E N| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hc : Cond272N B E s t) {Env : ℕ → ℝ} {Kenv KM : ℝ}
    (hmeasQ : ∀ (N : ℕ) (v : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2),
      AEStronglyMeasurable (fun ω => primBil (B.L N) (B.W N) (lkPath X (E N) N (v : ℝ) ω)
        (lkPath X (E N) N (v : ℝ) ω) (LoopData.idx (σ, a))) B.P)
    (hmeasG : ∀ (N : ℕ) (v : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2),
      AEStronglyMeasurable (fun ω => Decay.eG (B.L N) (B.W N) (lkPath X (E N) N (v : ℝ) ω)
        (gloop (B.L N) (B.W N) (X.H N (v : ℝ) ω) (zt (E N) (v : ℝ))) (LoopData.idx (σ, a))) B.P)
    (henvQ : ∀ (N : ℕ) (v : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2) (ω : Ω),
      ‖primBil (B.L N) (B.W N) (lkPath X (E N) N (v : ℝ) ω) (lkPath X (E N) N (v : ℝ) ω)
        (LoopData.idx (σ, a))‖ ≤ Env N)
    (henvG : ∀ (N : ℕ) (v : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2) (ω : Ω),
      ‖Decay.eG (B.L N) (B.W N) (lkPath X (E N) N (v : ℝ) ω)
        (gloop (B.L N) (B.W N) (X.H N (v : ℝ) ω) (zt (E N) (v : ℝ))) (LoopData.idx (σ, a))‖
        ≤ Env N)
    (hEnv0 : ∀ N, 0 ≤ Env N) (hKenv : 0 ≤ Kenv)
    (hEnvpoly : ∀ᶠ N : ℕ in atTop, Env N ≤ (N : ℝ) ^ Kenv) (hKM : 0 ≤ KM)
    (hlk : ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ σ : Fin 2 → Bool,
      FastDecay (B.L N) (B.ell N (s N) * (B.W N : ℝ) ^ τ) ((B.W N : ℝ) ^ (-D))
        (Step6.lkT X (E N) N (s N) σ))
    (hin : ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      (B.P (FDInputs X (E N) s t N ((B.W N : ℝ) ^ τ) ((N : ℝ) ^ (-D)) ((N : ℝ) ^ KM))ᶜ).toReal
        ≤ (N : ℝ) ^ (-D)) :
    Step6.FastDecayHypN X E s t (driftELKN X E) (driftEGN X E) := by
  have hP := B.isProbabilityMeasure
  intro τ hτ D hD
  set τ' : ℝ := τ / 2 with hτ'def
  have hτ' : 0 < τ' := by rw [hτ'def]; linarith
  set D₁ : ℝ := D + KM + Kenv + 4 with hD₁def
  have hD₁ : 0 < D₁ := by rw [hD₁def]; linarith
  filter_upwards [hlk τ hτ D hD, hin τ' hτ' D₁ hD₁, hEnvpoly,
    SumZeroDyn.flow_crudeN hE hs0 hst ht1 hc, B.eventually_le_W_rpow 3 hτ',
    SumZeroDyn.eventually_const_mul_rpow_le 8
      (show 2 + KM - D₁ < -D - 1 by rw [hD₁def]; linarith),
    SumZeroDyn.eventually_const_mul_rpow_le 1
      (show Kenv - D₁ < -D - 1 by rw [hD₁def]; linarith),
    eventually_ge_atTop 2] with N hlkN hinN hEnvN hcr hW3 herr1N herr2N hN2
  obtain ⟨hLN, hWN, _, _⟩ := hcr
  have hN2' : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hW0 : (0 : ℝ) < B.W N := by exact_mod_cast B.W_pos N
  set δ : ℝ := (N : ℝ) ^ (-D₁) with hδdef
  set M : ℝ := (N : ℝ) ^ KM with hMdef
  have hδ0 : (0 : ℝ) ≤ δ := Real.rpow_nonneg hN0.le _
  have hM0 : (0 : ℝ) ≤ M := Real.rpow_nonneg hN0.le _
  have hWL : (B.W N : ℝ) * (B.L N : ℝ) ≤ (N : ℝ) ^ (2 : ℝ) := by
    have h2 : (N : ℝ) ^ (2 : ℝ) = (N : ℝ) * (N : ℝ) := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
    have hW0' : (0 : ℝ) ≤ B.W N := Nat.cast_nonneg _
    have hL0' : (0 : ℝ) ≤ B.L N := Nat.cast_nonneg _
    rw [h2]; nlinarith
  -- `N^{-D} ≤ W^{-D}`
  have hWD : (N : ℝ) ^ (-D) ≤ (B.W N : ℝ) ^ (-D) := by
    have h1 : (0 : ℝ) < (B.W N : ℝ) ^ D := Real.rpow_pos_of_pos hW0 D
    have h2 : (B.W N : ℝ) ^ D ≤ (N : ℝ) ^ D := Real.rpow_le_rpow hW0.le hWN hD.le
    rw [Real.rpow_neg hW0.le, Real.rpow_neg hN0.le, ← one_div, ← one_div]
    exact one_div_le_one_div_of_le h1 h2
  have hsum2 : (N : ℝ) ^ (-D - 1) + (N : ℝ) ^ (-D - 1) ≤ (B.W N : ℝ) ^ (-D) := by
    have hmul : (N : ℝ) ^ (-D - 1) * (N : ℝ) ^ (1 : ℝ) = (N : ℝ) ^ (-D) := by
      rw [← Real.rpow_add hN0]; congr 1; ring
    have hp : (0 : ℝ) ≤ (N : ℝ) ^ (-D - 1) := Real.rpow_nonneg hN0.le _
    have : (N : ℝ) ^ (-D - 1) + (N : ℝ) ^ (-D - 1) ≤ (N : ℝ) ^ (-D) := by
      rw [← hmul, Real.rpow_one]; nlinarith
    exact this.trans hWD
  -- the two error budgets
  have herrEnv : Env N * δ ≤ (N : ℝ) ^ (-D - 1) := by
    have h1 : Env N * δ ≤ (N : ℝ) ^ Kenv * δ := mul_le_mul_of_nonneg_right hEnvN hδ0
    have he : (N : ℝ) ^ Kenv * δ = (N : ℝ) ^ (Kenv - D₁) := by
      rw [hδdef, ← Real.rpow_add hN0, sub_eq_add_neg]
    refine h1.trans ?_
    rw [he]
    calc (N : ℝ) ^ (Kenv - D₁) = 1 * (N : ℝ) ^ (Kenv - D₁) := by ring
      _ ≤ (N : ℝ) ^ (-D - 1) := herr2N
  have hcoefErr : ∀ cc : ℝ, 0 ≤ cc → cc ≤ 8 →
      cc * (B.W N : ℝ) * (B.L N : ℝ) * δ * M ≤ (N : ℝ) ^ (-D - 1) := by
    intro cc hcc0 hcc8
    have he : (N : ℝ) ^ (2 : ℝ) * δ * M = (N : ℝ) ^ (2 + KM - D₁) := by
      rw [hδdef, hMdef, ← Real.rpow_add hN0, ← Real.rpow_add hN0]
      congr 1; ring
    have hδM : (0 : ℝ) ≤ δ * M := mul_nonneg hδ0 hM0
    have hW0' : (0 : ℝ) ≤ (B.W N : ℝ) := Nat.cast_nonneg _
    have hL0' : (0 : ℝ) ≤ (B.L N : ℝ) := Nat.cast_nonneg _
    have hWL0 : (0 : ℝ) ≤ (B.W N : ℝ) * (B.L N : ℝ) := mul_nonneg hW0' hL0'
    have hstep : cc * (B.W N : ℝ) * (B.L N : ℝ) * δ * M ≤ 8 * ((N : ℝ) ^ (2 : ℝ) * δ * M) := by
      have hcc : cc * ((B.W N : ℝ) * (B.L N : ℝ)) ≤ 8 * ((B.W N : ℝ) * (B.L N : ℝ)) :=
        mul_le_mul_of_nonneg_right hcc8 hWL0
      calc cc * (B.W N : ℝ) * (B.L N : ℝ) * δ * M
          = cc * ((B.W N : ℝ) * (B.L N : ℝ)) * (δ * M) := by ring
        _ ≤ 8 * ((B.W N : ℝ) * (B.L N : ℝ)) * (δ * M) :=
            mul_le_mul_of_nonneg_right hcc hδM
        _ = 8 * (((B.W N : ℝ) * (B.L N : ℝ)) * (δ * M)) := by ring
        _ ≤ 8 * ((N : ℝ) ^ (2 : ℝ) * (δ * M)) := by
            have := mul_le_mul_of_nonneg_right hWL hδM
            linarith
        _ = 8 * ((N : ℝ) ^ (2 : ℝ) * δ * M) := by ring
    refine hstep.trans ?_
    rw [he]
    exact herr1N
  refine fun σ => ⟨hlkN σ, ?_⟩
  intro v hv
  set vv : TimeIcc s t N := ⟨v, hv⟩ with hvvdef
  have hv0 : 0 ≤ v := (hs0 N).trans hv.1
  have hv1 : v < 1 := hv.2.trans_lt (ht1 N)
  have hℓ1 : (1 : ℝ) ≤ B.ell N v := by
    have := one_le_ellHat (B.L N) (B.three_le_L N) hv0 hv1
    rw [Band.ell]; exact this
  have hWt1 : (1 : ℝ) ≤ (B.W N : ℝ) ^ τ' := by linarith
  -- the radius arithmetic `2 ℓ_v W^{τ'} + 1 ≤ ℓ_v W^τ`
  have hWW : (B.W N : ℝ) ^ τ' * (B.W N : ℝ) ^ τ' = (B.W N : ℝ) ^ τ := by
    rw [← Real.rpow_add hW0]; congr 1; rw [hτ'def]; ring
  have hrad : 2 * (B.ell N v * (B.W N : ℝ) ^ τ') + 1 ≤ B.ell N v * (B.W N : ℝ) ^ τ := by
    have h1 : 2 * (B.ell N v * (B.W N : ℝ) ^ τ') + 1
        ≤ B.ell N v * (3 * (B.W N : ℝ) ^ τ') := by nlinarith
    have h2 : B.ell N v * (3 * (B.W N : ℝ) ^ τ')
        ≤ B.ell N v * ((B.W N : ℝ) ^ τ' * (B.W N : ℝ) ^ τ') := by
      have : (3 : ℝ) * (B.W N : ℝ) ^ τ' ≤ (B.W N : ℝ) ^ τ' * (B.W N : ℝ) ^ τ' := by nlinarith
      nlinarith
    rw [← hWW]; linarith
  have hradG : B.ell N v * (B.W N : ℝ) ^ τ' ≤ B.ell N v * (B.W N : ℝ) ^ τ := by
    nlinarith [hrad, hWt1]
  constructor
  · -- the quadratic half
    have hgood : ∀ ω ∈ FDInputs X (E N) s t N ((B.W N : ℝ) ^ τ') δ M,
        FastDecay (B.L N) (2 * (B.ell N v * (B.W N : ℝ) ^ τ') + 1)
          (8 * (B.W N : ℝ) * (B.L N : ℝ) * δ * M)
          (fun a : LoopArg (B.L N) 2 => primBil (B.L N) (B.W N) (lkPath X (E N) N v ω)
            (lkPath X (E N) N v ω) (LoopData.idx (σ, a))) := by
      intro ω hω
      obtain ⟨hDd, _, hDb⟩ := hω vv
      exact fastDecay_primBil_lkPath X (E N) N v ω σ hδ0 hM0 hDd hDb
    have hE8 : (0 : ℝ) ≤ 8 * (B.W N : ℝ) * (B.L N : ℝ) * δ * M := by
      have hW0' : (0 : ℝ) ≤ B.W N := Nat.cast_nonneg _
      have hL0' : (0 : ℝ) ≤ B.L N := Nat.cast_nonneg _
      positivity
    have hres := fastDecay_integral_of_highProb (P := B.P)
      (G := FDInputs X (E N) s t N ((B.W N : ℝ) ^ τ') δ M) hE8 (hmeasQ N vv σ) hgood
      (fun ω a => henvQ N vv σ a ω)
    refine SumZeroDyn.FastDecay.mono (B.L N) hres hrad ?_
    have h1 : 8 * (B.W N : ℝ) * (B.L N : ℝ) * δ * M ≤ (N : ℝ) ^ (-D - 1) :=
      hcoefErr 8 (by norm_num) le_rfl
    have h2 : Env N * (B.P (FDInputs X (E N) s t N ((B.W N : ℝ) ^ τ') δ M)ᶜ).toReal
        ≤ (N : ℝ) ^ (-D - 1) := by
      refine le_trans (mul_le_mul_of_nonneg_left hinN (hEnv0 N)) herrEnv
    linarith [hsum2]
  · -- the `E^{(G)}` half
    have hgood : ∀ ω ∈ FDInputs X (E N) s t N ((B.W N : ℝ) ^ τ') δ M,
        FastDecay (B.L N) (B.ell N v * (B.W N : ℝ) ^ τ')
          (2 * (B.W N : ℝ) * (B.L N : ℝ) * M * δ)
          (fun a : LoopArg (B.L N) 2 => Decay.eG (B.L N) (B.W N) (lkPath X (E N) N v ω)
            (gloop (B.L N) (B.W N) (X.H N v ω) (zt (E N) v)) (LoopData.idx (σ, a))) := by
      intro ω hω
      obtain ⟨_, hLd, hDb⟩ := hω vv
      exact fastDecay_eG_lkPath X (E N) N v ω σ hLd hDb
    have hE2 : (0 : ℝ) ≤ 2 * (B.W N : ℝ) * (B.L N : ℝ) * M * δ := by
      have hW0' : (0 : ℝ) ≤ B.W N := Nat.cast_nonneg _
      have hL0' : (0 : ℝ) ≤ B.L N := Nat.cast_nonneg _
      positivity
    have hres := fastDecay_integral_of_highProb (P := B.P)
      (G := FDInputs X (E N) s t N ((B.W N : ℝ) ^ τ') δ M) hE2 (hmeasG N vv σ) hgood
      (fun ω a => henvG N vv σ a ω)
    refine SumZeroDyn.FastDecay.mono (B.L N) hres hradG ?_
    have h1 : 2 * (B.W N : ℝ) * (B.L N : ℝ) * M * δ ≤ (N : ℝ) ^ (-D - 1) := by
      have := hcoefErr 2 (by norm_num) (by norm_num)
      linarith [this, (by ring : 2 * (B.W N : ℝ) * (B.L N : ℝ) * M * δ
        = 2 * (B.W N : ℝ) * (B.L N : ℝ) * δ * M)]
    have h2 : Env N * (B.P (FDInputs X (E N) s t N ((B.W N : ℝ) ^ τ') δ M)ᶜ).toReal
        ≤ (N : ℝ) ^ (-D - 1) :=
      le_trans (mul_le_mul_of_nonneg_left hinN (hEnv0 N)) herrEnv
    linarith [hsum2]

open Real in
set_option maxHeartbeats 1000000 in
/-- **`|driftEG| ≤ W ℓ_u (W ℓ_u η_u)^{-4}`** (`UnifDetDom`), from (5.126) (`h526`), the decay of
`K` and the inputs `EGInputs`. The kernel constant `CK` (`n = 3`) is obtained once, uniformly in
`κ`, from `RBM.Band.norm_Kval_le_unif` (module docstring). -/
theorem unifDetDom_driftEG'N (X : Sample B) {E : ℕ → ℝ} {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hEκ : ∀ N, |E N| ≤ 2 - κ) {s t : ℕ → ℝ}
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hc : Cond272N B E s t) {Env : ℕ → ℝ} {Kenv : ℝ}
    (hmeasLK : ∀ (N : ℕ) (v : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2),
      AEStronglyMeasurable (fun ω => Decay.eG (B.L N) (B.W N) (lkPath X (E N) N (v : ℝ) ω)
        (lkPath X (E N) N (v : ℝ) ω) (LoopData.idx (σ, a))) B.P)
    (henvLK : ∀ (N : ℕ) (v : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2) (ω : Ω),
      ‖Decay.eG (B.L N) (B.W N) (lkPath X (E N) N (v : ℝ) ω) (lkPath X (E N) N (v : ℝ) ω)
        (LoopData.idx (σ, a))‖ ≤ Env N)
    (hEnv0 : ∀ N, 0 ≤ Env N) (hKenv : 0 ≤ Kenv)
    (hEnvpoly : ∀ᶠ N : ℕ in atTop, Env N ≤ (N : ℝ) ^ Kenv)
    (hintL : ∀ (N : ℕ) (v : TimeIcc s t N) (b : Bool) (x : ZMod (B.L N)),
      Integrable (fun ω => X.Lval (E N) N (v : ℝ) ω ⟨[b], [x]⟩) B.P)
    (h526 : UnifDetDom (fun N (p : TimeIcc s t N × ZMod (B.L N)) => ‖Step6.lk1 X (E N) N p.1 p.2‖)
      (fun N p => (B.scale (E N) N p.1)⁻¹ ^ 2))
    (hKd : ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ v : TimeIcc s t N,
      Decay.LoopDecay (B.L N) 3 (B.ell N (v : ℝ) * (N : ℝ) ^ τ) ((N : ℝ) ^ (-D))
        (B.Kval (E N) N (v : ℝ)))
    (hin : ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), HighProb B.P (fun N =>
      EGInputs X (E N) s t N ((N : ℝ) ^ τ) ((N : ℝ) ^ (-D)) ((N : ℝ) ^ τ))) :
    UnifDetDom (fun N (p : TimeIcc s t N × LoopData (B.L N) 2) =>
        ‖driftEG X (E N) N p.1 p.2.1 p.2.2‖)
      (fun N p => (B.W N : ℝ) * B.ell N p.1 * (B.scale (E N) N p.1)⁻¹ ^ 4) := by
  have hP := B.isProbabilityMeasure
  have hE : ∀ N, |E N| < 2 := fun N => by linarith [hEκ N]
  obtain ⟨CK, hCK0, hCK⟩ := B.norm_Kval_le_unif hκ0 hκ1 (n := 3) (by norm_num)
  intro τ hτ
  set τ₁ : ℝ := τ / 8 with hτ₁def
  have hτ₁ : 0 < τ₁ := by rw [hτ₁def]; linarith
  set D₁ : ℝ := 3 + Kenv + τ₁ + 4 with hD₁def
  have hD₁ : 0 < D₁ := by rw [hD₁def]; linarith
  filter_upwards [hin τ₁ hτ₁ D₁ hD₁ D₁ hD₁, h526 τ₁ hτ₁, hKd τ₁ hτ₁ D₁ hD₁,
    SumZeroDyn.flow_crudeN hE hs0 hst ht1 hc, hEnvpoly,
    eventually_rpow_neg_three_le_drift_targetN B hE hs0 hst ht1 hc,
    SumZeroDyn.eventually_const_mul_rpow_le (12 * exp 1 * (1 + CK))
      (show 3 * τ₁ < τ / 2 by rw [hτ₁def]; linarith),
    SumZeroDyn.eventually_const_mul_rpow_le 4
      (show 2 + τ₁ - D₁ < -(3 : ℝ) - 1 by rw [hD₁def]; linarith),
    SumZeroDyn.eventually_const_mul_rpow_le 1
      (show Kenv - D₁ < -(3 : ℝ) - 1 by rw [hD₁def]; linarith),
    SumZeroDyn.eventually_const_mul_rpow_le 2 (show τ / 2 < τ by linarith),
    eventually_ge_atTop 2] with
    N hgood h526N hKdN hcr hEnvN hlowN hmainN herr1N herr2N hfinN hN2
  obtain ⟨hLN, hWN, _, hu⟩ := hcr
  rintro ⟨v, q⟩
  have hN2' : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
  have hN1' : (1 : ℝ) ≤ (N : ℝ) := by linarith
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  set u : ℝ := (v : ℝ) with hudef
  have hu0 : 0 ≤ u := (hs0 N).trans v.2.1
  have hu1 : u < 1 := v.2.2.trans_lt (ht1 N)
  have hA : 1 ≤ B.scale (E N) N u := (hu v).1
  have hA0 : (0 : ℝ) < B.scale (E N) N u := lt_of_lt_of_le zero_lt_one hA
  have hAi1 : (B.scale (E N) N u)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hA
  have hAi0 : (0 : ℝ) ≤ (B.scale (E N) N u)⁻¹ := inv_nonneg.2 hA0.le
  have hell : (1 : ℝ) / 2 ≤ B.ell N u := by
    have := one_le_ellHat (B.L N) (B.three_le_L N) hu0 hu1
    rw [Band.ell]; linarith
  set Gt : ℝ := (B.W N : ℝ) * B.ell N u * (B.scale (E N) N u)⁻¹ ^ 4 with hGtdef
  have hGt0 : 0 ≤ Gt := by
    have hW : (0 : ℝ) ≤ B.W N := Nat.cast_nonneg _
    have hℓ0 : (0 : ℝ) ≤ B.ell N u := by linarith
    rw [hGtdef]; positivity
  have hGtlow : (N : ℝ) ^ (-(3 : ℝ)) ≤ Gt := hlowN v
  set Krad : ℝ := (N : ℝ) ^ τ₁ with hKraddef
  set δ : ℝ := (N : ℝ) ^ (-D₁) with hδdef
  have hKrad1 : (1 : ℝ) ≤ Krad := Real.one_le_rpow hN1' hτ₁.le
  have hKrad0 : (0 : ℝ) ≤ Krad := by linarith
  have hδ0 : (0 : ℝ) ≤ δ := Real.rpow_nonneg hN0.le _
  have hWLδ0 : (0 : ℝ) ≤ (B.W N : ℝ) * (B.L N : ℝ) * δ := by
    have hW : (0 : ℝ) ≤ B.W N := Nat.cast_nonneg _
    have hL : (0 : ℝ) ≤ B.L N := Nat.cast_nonneg _
    positivity
  -- the two integrability facts
  have hint1 : ∀ (b : Bool) (x : ZMod (B.L N)),
      Integrable (fun ω => lkPath X (E N) N u ω ⟨[b], [x]⟩) B.P :=
    fun b x => integrable_lkPath_one X (E N) N u b x (hintL N v b x)
  have hintLK : Integrable (fun ω => Decay.eG (B.L N) (B.W N) (lkPath X (E N) N u ω)
      (lkPath X (E N) N u ω) (LoopData.idx (q.1, q.2))) B.P :=
    Integrable.mono' (integrable_const (Env N)) (hmeasLK N v q.1 q.2)
      (Filter.Eventually.of_forall fun ω => henvLK N v q.1 q.2 ω)
  -- the `L - K` half, pathwise on the good set
  set c₁ : ℝ := 4 * exp 1 * (Krad + 2) * (Krad * Krad) * Gt
    + 2 * ((B.W N : ℝ) * (B.L N : ℝ) * δ) * Krad with hc₁def
  have hc₁0 : 0 ≤ c₁ := by
    have h1 : (0 : ℝ) ≤ 4 * exp 1 * (Krad + 2) * (Krad * Krad) * Gt := by positivity
    have h2 : (0 : ℝ) ≤ 2 * ((B.W N : ℝ) * (B.L N : ℝ) * δ) * Krad := by positivity
    rw [hc₁def]; linarith
  have hptLK : ∀ ω ∈ EGInputs X (E N) s t N Krad δ Krad,
      ‖Decay.eG (B.L N) (B.W N) (lkPath X (E N) N u ω) (lkPath X (E N) N u ω)
        (LoopData.idx (q.1, q.2))‖ ≤ c₁ := by
    intro ω hω
    obtain ⟨hDd, hΨ1, hΨ3⟩ := hω v
    have hxi1 : 0 ≤ X.xiLK (E N) N u ω 1 := X.xiLK_nonneg hA0.le
    have hxi3 : 0 ≤ X.xiLK (E N) N u ω 3 := X.xiLK_nonneg hA0.le
    have hX : ∀ (b : Bool) (x : ZMod (B.L N)),
        ‖lkPath X (E N) N u ω ⟨[b], [x]⟩‖ ≤ X.xiLK (E N) N u ω 1 * (B.scale (E N) N u)⁻¹ := by
      intro b x
      have := DriftBound.norm_lk_le X (E N) N u ω hA0.ne' (⟨[b], [x]⟩ : LoopIdx (ZMod (B.L N)))
        rfl (j := 1) rfl
      rwa [pow_one] at this
    have hY : ∀ J : LoopIdx (ZMod (B.L N)), J.WF → J.length = 3 →
        ‖lkPath X (E N) N u ω J‖ ≤ (X.xiLK (E N) N u ω 3 * (B.scale (E N) N u)⁻¹)
          * (B.scale (E N) N u)⁻¹ ^ 2 := by
      intro J hJ hlen
      have := DriftBound.norm_lk_le X (E N) N u ω hA0.ne' J hJ hlen
      calc ‖lkPath X (E N) N u ω J‖ ≤ X.xiLK (E N) N u ω 3 * (B.scale (E N) N u)⁻¹ ^ 3 := this
        _ = (X.xiLK (E N) N u ω 3 * (B.scale (E N) N u)⁻¹) * (B.scale (E N) N u)⁻¹ ^ 2 := by ring
    have hCΦ : X.xiLK (E N) N u ω 1 * (X.xiLK (E N) N u ω 3 * (B.scale (E N) N u)⁻¹)
        ≤ (Krad * Krad) * (B.scale (E N) N u)⁻¹ := by
      have h1 : X.xiLK (E N) N u ω 1 * X.xiLK (E N) N u ω 3 ≤ Krad * Krad :=
        mul_le_mul hΨ1 hΨ3 hxi3 hKrad0
      calc X.xiLK (E N) N u ω 1 * (X.xiLK (E N) N u ω 3 * (B.scale (E N) N u)⁻¹)
          = (X.xiLK (E N) N u ω 1 * X.xiLK (E N) N u ω 3) * (B.scale (E N) N u)⁻¹ := by ring
        _ ≤ (Krad * Krad) * (B.scale (E N) N u)⁻¹ := mul_le_mul_of_nonneg_right h1 hAi0
    exact norm_eG_two_le N (lkPath X (E N) N u ω) (lkPath X (E N) N u ω) q.1 q.2
      (Ξ := X.xiLK (E N) N u ω 1) (Φ := X.xiLK (E N) N u ω 3 * (B.scale (E N) N u)⁻¹)
      (C := Krad * Krad) (Ξb := Krad)
      (hE N) hu1 hA hell hKrad1 hδ0 hxi1 (by positivity) hX hY hDd hCΦ hΨ1
  have hbad : (B.P (EGInputs X (E N) s t N Krad δ Krad)ᶜ).toReal ≤ δ :=
    ENNReal.toReal_le_of_le_ofReal hδ0 hgood
  have hLKbound : ‖∫ ω, Decay.eG (B.L N) (B.W N) (lkPath X (E N) N u ω) (lkPath X (E N) N u ω)
      (LoopData.idx (q.1, q.2)) ∂B.P‖ ≤ c₁ + Env N * δ := by
    have := norm_integral_le_add_measure_compl (P := B.P)
      (f := fun ω => Decay.eG (B.L N) (B.W N) (lkPath X (E N) N u ω) (lkPath X (E N) N u ω)
        (LoopData.idx (q.1, q.2)))
      (hmeasLK N v q.1 q.2) (G := EGInputs X (E N) s t N Krad δ Krad) hc₁0 hptLK
      (fun ω => henvLK N v q.1 q.2 ω)
    refine this.trans ?_
    have := mul_le_mul_of_nonneg_left hbad (hEnv0 N)
    linarith
  -- the `K` half, deterministic
  set c₂ : ℝ := 4 * exp 1 * (Krad + 2) * (Krad * CK) * Gt
    + 2 * ((B.W N : ℝ) * (B.L N : ℝ) * δ) * Krad with hc₂def
  have hKbound : ‖Decay.eG (B.L N) (B.W N) (fun J => ∫ ω, lkPath X (E N) N u ω J ∂B.P)
      (B.Kval (E N) N u) (LoopData.idx (q.1, q.2))‖ ≤ c₂ := by
    have hX : ∀ (b : Bool) (x : ZMod (B.L N)),
        ‖(fun J => ∫ ω, lkPath X (E N) N u ω J ∂B.P) ⟨[b], [x]⟩‖
          ≤ (Krad * (B.scale (E N) N u)⁻¹) * (B.scale (E N) N u)⁻¹ := by
      intro b x
      have heq := norm_integral_lkPath_one X (E N) N u b x (hintL N v true x)
      have hle : ‖Step6.lk1 X (E N) N u x‖ ≤ Krad * (B.scale (E N) N u)⁻¹ ^ 2 := h526N (v, x)
      calc ‖(fun J => ∫ ω, lkPath X (E N) N u ω J ∂B.P) ⟨[b], [x]⟩‖
          = ‖Step6.lk1 X (E N) N u x‖ := heq
        _ ≤ Krad * (B.scale (E N) N u)⁻¹ ^ 2 := hle
        _ = (Krad * (B.scale (E N) N u)⁻¹) * (B.scale (E N) N u)⁻¹ := by ring
    have hY : ∀ J : LoopIdx (ZMod (B.L N)), J.WF → J.length = 3 →
        ‖B.Kval (E N) N u J‖ ≤ CK * (B.scale (E N) N u)⁻¹ ^ 2 := by
      intro J hJ hlen
      have := hCK (E N) (hEκ N) N u hu0 hu1 J hJ hlen
      simpa using this
    exact norm_eG_two_le N (fun J => ∫ ω, lkPath X (E N) N u ω J ∂B.P) (B.Kval (E N) N u) q.1 q.2
      (Ξ := Krad * (B.scale (E N) N u)⁻¹) (Φ := CK) (C := Krad * CK) (Ξb := Krad)
      (hE N) hu1 hA hell hKrad1 hδ0 (by positivity) (by positivity) hX hY (hKdN v)
      (le_of_eq (by ring)) (mul_le_of_le_one_right hKrad0 hAi1)
  -- assemble
  have hsplit := driftEG_eq_add X (E N) N u q.1 q.2 hint1 hintLK
  have htot : ‖driftEG X (E N) N v q.1 q.2‖ ≤ (c₁ + Env N * δ) + c₂ := by
    rw [show driftEG X (E N) N v q.1 q.2 = driftEG X (E N) N u q.1 q.2 from rfl, hsplit]
    exact (norm_add_le _ _).trans (add_le_add hLKbound hKbound)
  refine htot.trans ?_
  -- the `Ξ`-bookkeeping: one main term, two errors
  have hWL : (B.W N : ℝ) * (B.L N : ℝ) ≤ (N : ℝ) ^ (2 : ℝ) := by
    have h2 : (N : ℝ) ^ (2 : ℝ) = (N : ℝ) * (N : ℝ) := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
    have hW0 : (0 : ℝ) ≤ B.W N := Nat.cast_nonneg _
    have hL0 : (0 : ℝ) ≤ B.L N := Nat.cast_nonneg _
    rw [h2]
    exact mul_le_mul hWN hLN hL0 (hW0.trans hWN)
  have hmain : 4 * exp 1 * (Krad + 2) * (Krad * Krad) * Gt
      + 4 * exp 1 * (Krad + 2) * (Krad * CK) * Gt ≤ (N : ℝ) ^ (τ / 2) * Gt := by
    have hk3 : Krad ^ 3 = (N : ℝ) ^ (3 * τ₁) := by
      rw [hKraddef, ← Real.rpow_natCast ((N : ℝ) ^ τ₁) 3, ← Real.rpow_mul hN0.le]
      norm_num [mul_comm]
    have hstep : 4 * exp 1 * (Krad + 2) * (Krad * Krad)
        + 4 * exp 1 * (Krad + 2) * (Krad * CK)
        ≤ 12 * exp 1 * (1 + CK) * (N : ℝ) ^ (3 * τ₁) := by
      rw [← hk3]
      have he : (0 : ℝ) ≤ exp 1 := (exp_pos 1).le
      have h1 : Krad + 2 ≤ 3 * Krad := by linarith
      have h2 : Krad + CK ≤ Krad * (1 + CK) := add_le_mul_one_add hKrad1 hCK0
      have hn1 : (0 : ℝ) ≤ Krad * (Krad + CK) := mul_nonneg hKrad0 (by linarith)
      have hinner : (Krad + 2) * (Krad * (Krad + CK))
          ≤ (3 * Krad) * (Krad * (Krad * (1 + CK))) := by
        calc (Krad + 2) * (Krad * (Krad + CK)) ≤ (3 * Krad) * (Krad * (Krad + CK)) :=
              mul_le_mul_of_nonneg_right h1 hn1
          _ ≤ (3 * Krad) * (Krad * (Krad * (1 + CK))) := by
              refine mul_le_mul_of_nonneg_left ?_ (by linarith)
              exact mul_le_mul_of_nonneg_left h2 hKrad0
      calc 4 * exp 1 * (Krad + 2) * (Krad * Krad)
            + 4 * exp 1 * (Krad + 2) * (Krad * CK)
          = (4 * exp 1) * ((Krad + 2) * (Krad * (Krad + CK))) := by ring
        _ ≤ (4 * exp 1) * ((3 * Krad) * (Krad * (Krad * (1 + CK)))) :=
            mul_le_mul_of_nonneg_left hinner (by positivity)
        _ = 12 * exp 1 * (1 + CK) * Krad ^ 3 := by ring
    calc 4 * exp 1 * (Krad + 2) * (Krad * Krad) * Gt
          + 4 * exp 1 * (Krad + 2) * (Krad * CK) * Gt
        = (4 * exp 1 * (Krad + 2) * (Krad * Krad)
            + 4 * exp 1 * (Krad + 2) * (Krad * CK)) * Gt := by ring
      _ ≤ (12 * exp 1 * (1 + CK) * (N : ℝ) ^ (3 * τ₁)) * Gt :=
          mul_le_mul_of_nonneg_right hstep hGt0
      _ ≤ (N : ℝ) ^ (τ / 2) * Gt := mul_le_mul_of_nonneg_right hmainN hGt0
  have herr1 : 2 * ((B.W N : ℝ) * (B.L N : ℝ) * δ) * Krad
      + 2 * ((B.W N : ℝ) * (B.L N : ℝ) * δ) * Krad ≤ (N : ℝ) ^ (-(3 : ℝ) - 1) := by
    have he : (N : ℝ) ^ (2 : ℝ) * δ * Krad = (N : ℝ) ^ (2 + τ₁ - D₁) := by
      rw [hδdef, hKraddef, ← Real.rpow_add hN0, ← Real.rpow_add hN0]
      congr 1; ring
    have hmono : 2 * ((B.W N : ℝ) * (B.L N : ℝ) * δ) * Krad
        + 2 * ((B.W N : ℝ) * (B.L N : ℝ) * δ) * Krad ≤ 4 * ((N : ℝ) ^ (2 : ℝ) * δ * Krad) := by
      have h1 : (B.W N : ℝ) * (B.L N : ℝ) * δ ≤ (N : ℝ) ^ (2 : ℝ) * δ :=
        mul_le_mul_of_nonneg_right hWL hδ0
      exact two_mul_add_two_mul_le hKrad0 h1
    refine hmono.trans ?_
    rw [he]
    exact herr1N
  have herr2 : Env N * δ ≤ (N : ℝ) ^ (-(3 : ℝ) - 1) := by
    have h1 : Env N * δ ≤ (N : ℝ) ^ Kenv * δ := mul_le_mul_of_nonneg_right hEnvN hδ0
    have he : (N : ℝ) ^ Kenv * δ = (N : ℝ) ^ (Kenv - D₁) := by
      rw [hδdef, ← Real.rpow_add hN0, sub_eq_add_neg]
    refine h1.trans ?_
    rw [he]
    calc (N : ℝ) ^ (Kenv - D₁) = 1 * (N : ℝ) ^ (Kenv - D₁) := by ring
      _ ≤ (N : ℝ) ^ (-(3 : ℝ) - 1) := herr2N
  have hsumerr : (N : ℝ) ^ (-(3 : ℝ) - 1) + (N : ℝ) ^ (-(3 : ℝ) - 1) ≤ Gt := by
    have hmul : (N : ℝ) ^ (-(3 : ℝ) - 1) * (N : ℝ) ^ (1 : ℝ) = (N : ℝ) ^ (-(3 : ℝ)) := by
      rw [← Real.rpow_add hN0]; congr 1; ring
    have hp : (0 : ℝ) ≤ (N : ℝ) ^ (-(3 : ℝ) - 1) := Real.rpow_nonneg hN0.le _
    have h2 : (N : ℝ) ^ (-(3 : ℝ) - 1) + (N : ℝ) ^ (-(3 : ℝ) - 1) ≤ (N : ℝ) ^ (-(3 : ℝ)) := by
      rw [← hmul, Real.rpow_one]
      exact add_self_le_mul_two_le hp hN2'
    exact h2.trans hGtlow
  have hfin : (N : ℝ) ^ (τ / 2) * Gt + Gt ≤ (N : ℝ) ^ τ * Gt := by
    have h1 : (1 : ℝ) ≤ (N : ℝ) ^ (τ / 2) := Real.one_le_rpow hN1' (by linarith)
    have h2 : (N : ℝ) ^ (τ / 2) + 1 ≤ (N : ℝ) ^ τ := by linarith [hfinN]
    exact mul_add_le_mul_of_add_one_le h2 hGt0
  rw [hc₁def, hc₂def]
  exact final_arith_eg hmain herr1 herr2 hsumerr hfin

/-- **The drift bound `Step6.DriftBoundN` for `driftEGN`**, under the hypotheses of
`unifDetDom_driftEG'N`. No energy-dependent constant is fixed here. -/
theorem driftBound_driftEG'N (X : Sample B) {E : ℕ → ℝ} {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hEκ : ∀ N, |E N| ≤ 2 - κ) {s t : ℕ → ℝ}
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hc : Cond272N B E s t) {Env : ℕ → ℝ} {Kenv : ℝ}
    (hmeasLK : ∀ (N : ℕ) (v : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2),
      AEStronglyMeasurable (fun ω => Decay.eG (B.L N) (B.W N) (lkPath X (E N) N (v : ℝ) ω)
        (lkPath X (E N) N (v : ℝ) ω) (LoopData.idx (σ, a))) B.P)
    (henvLK : ∀ (N : ℕ) (v : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2) (ω : Ω),
      ‖Decay.eG (B.L N) (B.W N) (lkPath X (E N) N (v : ℝ) ω) (lkPath X (E N) N (v : ℝ) ω)
        (LoopData.idx (σ, a))‖ ≤ Env N)
    (hEnv0 : ∀ N, 0 ≤ Env N) (hKenv : 0 ≤ Kenv)
    (hEnvpoly : ∀ᶠ N : ℕ in atTop, Env N ≤ (N : ℝ) ^ Kenv)
    (hintL : ∀ (N : ℕ) (v : TimeIcc s t N) (b : Bool) (x : ZMod (B.L N)),
      Integrable (fun ω => X.Lval (E N) N (v : ℝ) ω ⟨[b], [x]⟩) B.P)
    (h526 : UnifDetDom (fun N (p : TimeIcc s t N × ZMod (B.L N)) => ‖Step6.lk1 X (E N) N p.1 p.2‖)
      (fun N p => (B.scale (E N) N p.1)⁻¹ ^ 2))
    (hKd : ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ v : TimeIcc s t N,
      Decay.LoopDecay (B.L N) 3 (B.ell N (v : ℝ) * (N : ℝ) ^ τ) ((N : ℝ) ^ (-D))
        (B.Kval (E N) N (v : ℝ)))
    (hin : ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), HighProb B.P (fun N =>
      EGInputs X (E N) s t N ((N : ℝ) ^ τ) ((N : ℝ) ^ (-D)) ((N : ℝ) ^ τ))) :
    Step6.DriftBoundN B E s t (driftEGN X E) :=
  Step6.driftBound_of_5133N (fun N => by linarith [hEκ N]) ht1
    (unifDetDom_driftEG'N X hκ0 hκ1 hEκ hs0 hst ht1 hc hmeasLK henvLK hEnv0 hKenv hEnvpoly
      hintL h526 hKd hin)

set_option maxHeartbeats 1000000 in
/-- **(2.80) for the flow.** No energy-dependent constant is fixed here itself; assembled from
`sharpExpect_of_hierarchyN`/`hierarchyN_driftSplit` and `fastDecayHyp_driftSplit'N`,
`unifDetDom_driftELK'N`, `driftBound_driftEG'N`. The hierarchy hypotheses
(`hcont,hintL2,hintQ,hintG,hEL,hintU1,hintU2`) carry the extra diagonal binder `∀N₀` that
`hierarchyN_driftSplit` requires (module docstring). -/
theorem sharpExpect_step6_driftEG'N (X : Sample B) {E : ℕ → ℝ} {κ : ℝ} (hκ0 : 0 < κ)
    (hκ1 : κ ≤ 1) (hEκ : ∀ N, |E N| ≤ 2 - κ) {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hc : Cond272N B E s t)
    -- the analytic inputs of the hierarchy, diagonal-shaped
    (hcont : ∀ N₀ N (u : TimeIcc s t N) (σ : Fin 2 → Bool) (b : LoopArg (B.L N) 2),
      ContinuousOn (fun q : ℝ => Step6.lkT X (E N₀) N q σ b) (Set.Icc (s N) ((u : ℝ))))
    (hintL2 : ∀ N₀ N (v : ℝ), 0 < v → v < 1 → ∀ (σ : Fin 2 → Bool) (b : LoopArg (B.L N) 2),
      Integrable (fun ω => X.Lval (E N₀) N v ω (LoopData.idx (σ, b))) B.P)
    (hintQ : ∀ N₀ N (v : ℝ), 0 < v → v < 1 → ∀ (σ : Fin 2 → Bool) (b : LoopArg (B.L N) 2),
      Integrable (fun ω => primBil (B.L N) (B.W N) (lkPath X (E N₀) N v ω)
        (lkPath X (E N₀) N v ω) (LoopData.idx (σ, b))) B.P)
    (hintG : ∀ N₀ N (v : ℝ), 0 < v → v < 1 → ∀ (σ : Fin 2 → Bool) (b : LoopArg (B.L N) 2),
      Integrable (fun ω => Decay.eG (B.L N) (B.W N) (lkPath X (E N₀) N v ω)
        (gloop (B.L N) (B.W N) (X.H N v ω) (zt (E N₀) v)) (LoopData.idx (σ, b))) B.P)
    (hEL : ∀ N₀ N (v : ℝ), 0 < v → v < 1 → ∀ (σ : Fin 2 → Bool) (b : LoopArg (B.L N) 2),
      HasDerivAt (fun q : ℝ => X.ELval (E N₀) N q (LoopData.idx (σ, b)))
        (∫ ω, (Gauss.eGterm (B.L N) (B.W N) (mSigma (E N₀)) (X.H N v ω) (zt (E N₀) v)
            (LoopData.idx (σ, b))
          + primRhs (B.L N) (B.W N) (X.Lval (E N₀) N v ω) (LoopData.idx (σ, b))) ∂B.P) v)
    (hintU1 : ∀ N₀ N (u : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2),
      IntervalIntegrable (fun v : ℝ => Uker (B.L N) (xiOf (mSigma (E N₀)) σ) ((v : ℝ) : ℂ)
        (((u : ℝ)) : ℂ) (driftELK X (E N₀) N v σ) a) volume (s N) (u : ℝ))
    (hintU2 : ∀ N₀ N (u : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2),
      IntervalIntegrable (fun v : ℝ => Uker (B.L N) (xiOf (mSigma (E N₀)) σ) ((v : ℝ) : ℂ)
        (((u : ℝ)) : ℂ) (driftEG X (E N₀) N v σ) a) volume (s N) (u : ℝ))
    -- measurability and the crude envelope
    {Env : ℕ → ℝ} {Kenv KM : ℝ}
    (hmeasQ : ∀ (N : ℕ) (v : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2),
      AEStronglyMeasurable (fun ω => primBil (B.L N) (B.W N) (lkPath X (E N) N (v : ℝ) ω)
        (lkPath X (E N) N (v : ℝ) ω) (LoopData.idx (σ, a))) B.P)
    (hmeasG : ∀ (N : ℕ) (v : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2),
      AEStronglyMeasurable (fun ω => Decay.eG (B.L N) (B.W N) (lkPath X (E N) N (v : ℝ) ω)
        (gloop (B.L N) (B.W N) (X.H N (v : ℝ) ω) (zt (E N) (v : ℝ))) (LoopData.idx (σ, a))) B.P)
    (hmeasLK : ∀ (N : ℕ) (v : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2),
      AEStronglyMeasurable (fun ω => Decay.eG (B.L N) (B.W N) (lkPath X (E N) N (v : ℝ) ω)
        (lkPath X (E N) N (v : ℝ) ω) (LoopData.idx (σ, a))) B.P)
    (henvQ : ∀ (N : ℕ) (v : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2) (ω : Ω),
      ‖primBil (B.L N) (B.W N) (lkPath X (E N) N (v : ℝ) ω) (lkPath X (E N) N (v : ℝ) ω)
        (LoopData.idx (σ, a))‖ ≤ Env N)
    (henvG : ∀ (N : ℕ) (v : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2) (ω : Ω),
      ‖Decay.eG (B.L N) (B.W N) (lkPath X (E N) N (v : ℝ) ω)
        (gloop (B.L N) (B.W N) (X.H N (v : ℝ) ω) (zt (E N) (v : ℝ))) (LoopData.idx (σ, a))‖
        ≤ Env N)
    (henvLK : ∀ (N : ℕ) (v : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2) (ω : Ω),
      ‖Decay.eG (B.L N) (B.W N) (lkPath X (E N) N (v : ℝ) ω) (lkPath X (E N) N (v : ℝ) ω)
        (LoopData.idx (σ, a))‖ ≤ Env N)
    (hEnv0 : ∀ N, 0 ≤ Env N) (hKenv : 0 ≤ Kenv) (hKM : 0 ≤ KM)
    (hEnvpoly : ∀ᶠ N : ℕ in atTop, Env N ≤ (N : ℝ) ^ Kenv)
    -- Lemma 5.9 and the counts (5.76)
    (hlk : ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ σ : Fin 2 → Bool,
      FastDecay (B.L N) (B.ell N (s N) * (B.W N : ℝ) ^ τ) ((B.W N : ℝ) ^ (-D))
        (Step6.lkT X (E N) N (s N) σ))
    (hin59 : ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      (B.P (FDInputs X (E N) s t N ((B.W N : ℝ) ^ τ) ((N : ℝ) ^ (-D)) ((N : ℝ) ^ KM))ᶜ).toReal
        ≤ (N : ℝ) ^ (-D))
    (hinQ : ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), HighProb B.P (fun N =>
      QuadInputs X (E N) s t N ((N : ℝ) ^ τ) ((N : ℝ) ^ (-D)) ((N : ℝ) ^ τ)))
    (hinG : ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), HighProb B.P (fun N =>
      EGInputs X (E N) s t N ((N : ℝ) ^ τ) ((N : ℝ) ^ (-D)) ((N : ℝ) ^ τ)))
    (hKd : ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ v : TimeIcc s t N,
      Decay.LoopDecay (B.L N) 3 (B.ell N (v : ℝ) * (N : ℝ) ^ τ) ((N : ℝ) ^ (-D))
        (B.Kval (E N) N (v : ℝ)))
    -- (5.132), (5.127), `quad11`, and the `1`-loop integrability
    (h5132 : UnifDetDom (fun N (u : LoopData (B.L N) 2) => X.expErr (E N) N (s N) u.idx)
      (fun N _ => (B.scale (E N) N (s N))⁻¹ ^ 3))
    (h527 : Step6.Eq527N X E s t)
    (hq11 : UnifDetDom (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) =>
      ‖Step6.quad11 X (E N) N p.1 p.2.1 p.2.2‖) (fun N p => (B.scale (E N) N p.1)⁻¹ ^ 2))
    (hintL1 : ∀ (N : ℕ) (v : TimeIcc s t N) (b : Bool) (x : ZMod (B.L N)),
      Integrable (fun ω => X.Lval (E N) N (v : ℝ) ω ⟨[b], [x]⟩) B.P) :
    UnifDetDom (fun N (p : TimeIcc s t N × LoopData (B.L N) 2) => X.expErr (E N) N p.1 p.2.idx)
      (fun N _ => (B.scale (E N) N (t N))⁻¹ ^ 3) := by
  have hE : ∀ N, |E N| < 2 := fun N => by linarith [hEκ N]
  have hE2 : ∀ N, |E N| ≤ 2 := fun N => by linarith [hEκ N]
  exact Step6.sharpExpect_of_hierarchyN X hκ0 hκ1 hEκ hs0 hst ht1 hc
    (hierarchyN_driftSplit X hE2 hs0 ht1 hcont hintL2 hintQ hintG hEL hintU1 hintU2)
    (fastDecayHyp_driftSplit'N X hE hs0 hst ht1 hc hmeasQ hmeasG henvQ henvG hEnv0 hKenv
      hEnvpoly hKM hlk hin59)
    h5132
    (Step6.driftBound_of_5133N hE ht1
      (unifDetDom_driftELK'N X hE hs0 hst ht1 hc hmeasQ henvQ hEnv0 hKenv hEnvpoly
        (by norm_num) (eventually_rpow_neg_three_le_drift_targetN B hE hs0 hst ht1 hc) hinQ))
    (driftBound_driftEG'N X hκ0 hκ1 hEκ hs0 hst ht1 hc hmeasLK henvLK hEnv0 hKenv hEnvpoly
      hintL1 (Step6.lemma515N X hκ0 hκ1 hEκ hs0 ht1 h527 hq11) hKd hinG)

end WindowN

end RBM
