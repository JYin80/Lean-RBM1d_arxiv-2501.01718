/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.FlowContInt
import RBM1D.EnergyN.Gauss.Step6WindowStep

/-!
# Step 6 inputs from the loop-decay pair, at an `N`-dependent energy

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, §5.8, (5.126)–(5.136), and §2.7,
(2.71), (2.80).

At an `N`-dependent energy `E : ℕ → ℝ`: the predicate `RBM.Step6LoopDecayPairN` (Lemma 5.9 for
`L` and `L - K`, uniformly on the window) and six statements that use only it: the inputs
`QuadInputs`, `EGInputs`, `FDInputs` with high probability (`RBM.highProb_quadInputs_pairN`,
`RBM.highProb_egInputs_pairN`, `RBM.exists_fdInputs_highProb_pairN`), the fast decay of `L - K`
at `s` (`RBM.fastDecay_lkT_of_pairN`, `RBM.Gauss.hlk_gauss_pairN`), and the (2.71) half of the
step (`RBM.Gauss.bounds_step_gauss_window_pairN`). The rest of the Step 6 window
(`step6LoopDecayPair_gauss_plainN`, `xiLK_le_one_gauss_plainN`, `eta_rpow_neg_one_le_windowN`,
`thm221RegN_gauss`, `boundsNInput_gauss`) is in
`RBM1D/EnergyN/Gauss/Thm221RegGauss.lean`.

## The energy

None of these fixes an energy-dependent constant; every exponent-bearing constant this file
uses (`KM` from `RBM.exists_norm_lkPath_le_rpowN`, the envelope exponent from
`RBM.exists_env_windowN`/`RBM.Gauss.bounds_step_gauss_windowN`) is fixed in
`RBM1D/EnergyN/Gauss/Step6WindowStep.lean`.
-/

open MeasureTheory Filter

namespace RBM

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- **Lemma 5.9 for `L` and `L - K`, uniformly on the window**, at an `N`-dependent energy: for
every loop length `m ≥ 1` and `τ, D > 0`, with high probability `lkPath` and `gloop` have the
decay `LoopDecay` at scale `ℓ_u N^τ` with error `N^{-D}` at all `u ∈ [s, t]`. No energy-dependent
constant is fixed here (only `E ↦ E N` inside a `∀ N`-quantified body). -/
def Step6LoopDecayPairN {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B)
    (E : ℕ → ℝ) (s t : ℕ → ℝ) : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∀ τ D : ℝ, 0 < τ → 0 < D →
    HighProb B.P (fun N => {ω | ∀ u : TimeIcc s t N,
      Decay.LoopDecay (B.L N) m (B.ell N (u : ℝ) * (N : ℝ) ^ τ) ((N : ℝ) ^ (-D))
        (lkPath X (E N) N (u : ℝ) ω)
      ∧ Decay.LoopDecay (B.L N) m (B.ell N (u : ℝ) * (N : ℝ) ^ τ) ((N : ℝ) ^ (-D))
        (gloop (B.L N) (B.W N) (X.H N (u : ℝ) ω) (zt (E N) (u : ℝ)))})

/-- **`RBM.QuadInputs` holds with high probability**, from `Step6LoopDecayPairN` and
`Ξ^{(L-K)}_2 ≺ 1`; the proof uses `RBM.highProb_flowXiLK_leN`
(`EnergyN/Gauss/Step6WindowStep.lean`). -/
theorem highProb_quadInputs_pairN (X : Sample B) {E : ℕ → ℝ} {s t : ℕ → ℝ}
    (hLD : Step6LoopDecayPairN X E s t)
    (hxi2 : StochDom B.P (fun N u ω => Step3.flowXiLK X (E N) s t 2 N u ω)
      fun _ _ _ => (1 : ℝ)) :
    ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), HighProb B.P (fun N =>
      QuadInputs X (E N) s t N ((N : ℝ) ^ τ) ((N : ℝ) ^ (-D)) ((N : ℝ) ^ τ)) := by
  intro τ hτ D hD
  refine ((hLD 2 (by norm_num) τ D hτ hD).inter
    (highProb_flowXiLK_leN X hxi2 hτ)).mono (Eventually.of_forall fun N ω hω u => ?_)
  exact ⟨(hω.1 u).1, hω.2 u⟩

/-- **`RBM.EGInputs` holds with high probability**, from `Step6LoopDecayPairN` and
`Ξ^{(L-K)}_1, Ξ^{(L-K)}_3 ≺ 1`; the proof uses `RBM.highProb_flowXiLK_leN`. -/
theorem highProb_egInputs_pairN (X : Sample B) {E : ℕ → ℝ} {s t : ℕ → ℝ}
    (hLD : Step6LoopDecayPairN X E s t)
    (hxi1 : StochDom B.P (fun N u ω => Step3.flowXiLK X (E N) s t 1 N u ω)
      fun _ _ _ => (1 : ℝ))
    (hxi3 : StochDom B.P (fun N u ω => Step3.flowXiLK X (E N) s t 3 N u ω)
      fun _ _ _ => (1 : ℝ)) :
    ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), HighProb B.P (fun N =>
      EGInputs X (E N) s t N ((N : ℝ) ^ τ) ((N : ℝ) ^ (-D)) ((N : ℝ) ^ τ)) := by
  intro τ hτ D hD
  refine (((hLD 3 (by norm_num) τ D hτ hD).inter
    (highProb_flowXiLK_leN X hxi1 hτ)).inter
    (highProb_flowXiLK_leN X hxi3 hτ)).mono (Eventually.of_forall fun N ω hω u => ?_)
  exact ⟨(hω.1.1 u).1, hω.1.2 u, hω.2 u⟩

/-- **`FDInputs` with high probability**: there is `KM ≥ 0` such that, for all `τ, D > 0`,
eventually the complement of `FDInputs` has probability at most `N^{-D}`. The proof uses
`RBM.exists_norm_lkPath_le_rpowN`. -/
theorem exists_fdInputs_highProb_pairN (X : Sample B) {E : ℕ → ℝ} {κ : ℝ} (hκ0 : 0 < κ)
    (hκ1 : κ ≤ 1) (hEκ : ∀ N, |E N| ≤ 2 - κ) {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N)
    (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 ≤ c)
    (hη : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-c) ≤ etaT (E N) (t N))
    (hLD : Step6LoopDecayPairN X E s t) :
    ∃ KM : ℝ, 0 ≤ KM ∧ ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      (B.P (FDInputs X (E N) s t N ((B.W N : ℝ) ^ τ) ((N : ℝ) ^ (-D)) ((N : ℝ) ^ KM))ᶜ).toReal
        ≤ (N : ℝ) ^ (-D) := by
  obtain ⟨KM, hKM0, hM⟩ := exists_norm_lkPath_le_rpowN X hκ0 hκ1 hEκ hs0 ht1 hc0 hη
  refine ⟨KM, hKM0, fun τ hτ D hD => ?_⟩
  have hdec := hLD 3 (by norm_num) (τ / 4) D (by linarith) hD D hD
  filter_upwards [hdec, hM, B.bandwidth, eventually_ge_atTop 1] with N hdN hMN hbwN hN1
  have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hnn : (0 : ℝ) ≤ (N : ℝ) ^ (-D) := Real.rpow_nonneg hN0.le _
  have hWt : (N : ℝ) ^ (τ / 4) ≤ (B.W N : ℝ) ^ τ := by
    have h1 : (N : ℝ) ^ ((1 / 2 + B.c) * τ) ≤ (B.W N : ℝ) ^ τ := by
      rw [Real.rpow_mul hN0.le]
      exact Real.rpow_le_rpow (Real.rpow_nonneg hN0.le _) hbwN hτ.le
    refine le_trans (Real.rpow_le_rpow_of_exponent_le hN1' ?_) h1
    have := B.c_pos
    nlinarith
  refine ENNReal.toReal_le_of_le_ofReal hnn (le_trans (measure_mono ?_) hdN)
  refine Set.compl_subset_compl.2 fun ω hω v => ?_
  have hell0 : (0 : ℝ) ≤ B.ell N (v : ℝ) :=
    le_trans zero_le_one (one_le_ellHat (B.L N) (B.three_le_L N)
      ((hs0 N).trans v.2.1) (v.2.2.trans_lt (ht1 N)))
  have hrad : B.ell N (v : ℝ) * (N : ℝ) ^ (τ / 4)
      ≤ B.ell N (v : ℝ) * (B.W N : ℝ) ^ τ := mul_le_mul_of_nonneg_left hWt hell0
  exact ⟨(hω v).1.mono (B.L N) (by norm_num) hrad le_rfl,
    (hω v).2.mono (B.L N) le_rfl hrad le_rfl,
    fun J hJ h2 => hMN v ω J hJ h2⟩

/-- **The fast decay of `L - K` at `s`**, for both charges, from `Step6LoopDecayPairN`, a polynomial
bound on `lkPath` and integrability; `RBM.integral_lkPath_eq_lkT` (energy-free) is applied at
`E N`. -/
theorem fastDecay_lkT_of_pairN (X : Sample B) {E : ℕ → ℝ} {s t : ℕ → ℝ}
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hLD : Step6LoopDecayPairN X E s t) {KM : ℝ} (hKM0 : 0 ≤ KM)
    (hM : ∀ᶠ N : ℕ in atTop, ∀ (v : TimeIcc s t N) (ω : Ω) (J : LoopIdx (ZMod (B.L N))),
      J.WF → J.length ≤ 2 → ‖lkPath X (E N) N (v : ℝ) ω J‖ ≤ (N : ℝ) ^ KM)
    (hmeas : ∀ (N : ℕ) (J : LoopIdx (ZMod (B.L N))),
      AEStronglyMeasurable (fun ω => lkPath X (E N) N (s N) ω J) B.P)
    (hint : ∀ (N : ℕ) (J : LoopIdx (ZMod (B.L N))), J.WF → 1 ≤ J.length →
      Integrable (fun ω => X.Lval (E N) N (s N) ω J) B.P) :
    ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ σ : Fin 2 → Bool,
      FastDecay (B.L N) (B.ell N (s N) * (B.W N : ℝ) ^ τ) ((B.W N : ℝ) ^ (-D))
        (Step6.lkT X (E N) N (s N) σ) := by
  intro τ hτ D hD
  have hP := B.isProbabilityMeasure
  have hdec := hLD 2 (by norm_num) (τ / 4) (D + 1) (by linarith) (by linarith)
  filter_upwards [hdec (D + KM + 1) (by linarith), hM, B.bandwidth, B.dim,
    eventually_ge_atTop 1,
    SumZeroDyn.eventually_const_mul_rpow_le 2 (show -(D + 1) < -D by linarith)] with
    N hpN hMN hbwN hdimN hN1 htwoN
  have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hW1 : (1 : ℝ) ≤ (B.W N : ℝ) := by exact_mod_cast B.W_pos N
  have hWN : (B.W N : ℝ) ≤ (N : ℝ) := by
    have h1 : B.W N ≤ B.W N * B.L N :=
      Nat.le_mul_of_pos_right _ (by have := B.three_le_L N; omega)
    exact_mod_cast h1.trans hdimN.1
  have hWt : (N : ℝ) ^ (τ / 4) ≤ (B.W N : ℝ) ^ τ := by
    have h1 : (N : ℝ) ^ ((1 / 2 + B.c) * τ) ≤ (B.W N : ℝ) ^ τ := by
      rw [Real.rpow_mul hN0.le]
      exact Real.rpow_le_rpow (Real.rpow_nonneg hN0.le _) hbwN hτ.le
    refine le_trans (Real.rpow_le_rpow_of_exponent_le hN1' ?_) h1
    have := B.c_pos
    nlinarith
  have hWD : (N : ℝ) ^ (-D) ≤ (B.W N : ℝ) ^ (-D) := by
    rw [Real.rpow_neg (by positivity), Real.rpow_neg (by positivity)]
    exact inv_anti₀ (Real.rpow_pos_of_pos (by linarith) D)
      (Real.rpow_le_rpow (by linarith) hWN hD.le)
  intro σ
  set G : Set Ω := {ω | ∀ u : TimeIcc s t N,
      Decay.LoopDecay (B.L N) 2 (B.ell N (u : ℝ) * (N : ℝ) ^ (τ / 4)) ((N : ℝ) ^ (-(D + 1)))
        (lkPath X (E N) N (u : ℝ) ω)
      ∧ Decay.LoopDecay (B.L N) 2 (B.ell N (u : ℝ) * (N : ℝ) ^ (τ / 4)) ((N : ℝ) ^ (-(D + 1)))
        (gloop (B.L N) (B.W N) (X.H N (u : ℝ) ω) (zt (E N) (u : ℝ)))} with hGdef
  have hgood : ∀ ω ∈ G, FastDecay (B.L N) (B.ell N (s N) * (N : ℝ) ^ (τ / 4))
      ((N : ℝ) ^ (-(D + 1)))
      (fun b : LoopArg (B.L N) 2 => lkPath X (E N) N (s N) ω (LoopData.idx (σ, b))) := by
    intro ω hω
    exact ((hω ⟨s N, le_rfl, hst N⟩).1).fastDecay (B.L N) (List.ofFn σ) (by simp)
  have hFD := fastDecay_integral_of_highProb (P := B.P) (L := B.L N) (n := 2)
    (δ := (N : ℝ) ^ (-(D + 1))) (Env := (N : ℝ) ^ KM)
    (A := fun ω (b : LoopArg (B.L N) 2) => lkPath X (E N) N (s N) ω (LoopData.idx (σ, b)))
    (G := G) (Real.rpow_nonneg hN0.le _)
    (fun b => hmeas N (LoopData.idx (σ, b))) hgood
    (fun ω b => hMN ⟨s N, le_rfl, hst N⟩ ω (LoopData.idx (σ, b)) (LoopData.idx_wf _) (by simp))
  rw [integral_lkPath_eq_lkT X (E N) N (s N) σ (hint N)] at hFD
  refine SumZeroDyn.FastDecay.mono (B.L N) hFD ?_ ?_
  · have hell0 : (0 : ℝ) ≤ B.ell N (s N) :=
      le_trans zero_le_one (one_le_ellHat (B.L N) (B.three_le_L N) (hs0 N)
        ((hst N).trans_lt (ht1 N)))
    exact mul_le_mul_of_nonneg_left hWt hell0
  · have hq : (B.P Gᶜ).toReal ≤ (N : ℝ) ^ (-(D + KM + 1)) :=
      ENNReal.toReal_le_of_le_ofReal (Real.rpow_nonneg hN0.le _) hpN
    have hKM : (0 : ℝ) ≤ (N : ℝ) ^ KM := Real.rpow_nonneg hN0.le _
    have hmul : (N : ℝ) ^ KM * (B.P Gᶜ).toReal ≤ (N : ℝ) ^ (-(D + 1)) := by
      refine le_trans (mul_le_mul_of_nonneg_left hq hKM) (le_of_eq ?_)
      rw [← Real.rpow_add hN0]; congr 1; ring
    linarith [hWD]

end RBM

namespace RBM.Gauss

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- **The fast decay of `L - K` at `s` for the Gaussian model**, from `Step6LoopDecayPairN`. The
proof uses `RBM.exists_norm_lkPath_le_rpowN` and `RBM.fastDecay_lkT_of_pairN`; the deterministic
Gaussian facts (`RBM.Gauss.continuous_lkPath_gauss`, `RBM.Gauss.etaT_pos_of_lt_one`,
`RBM.Gauss.abs_im_zt`, energy-free) are applied at `E N`. -/
theorem hlk_gauss_pairN (d : Dims) {E : ℕ → ℝ} {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hEκ : ∀ N, |E N| ≤ 2 - κ)
    {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    {c : ℝ} (hc0 : 0 ≤ c) (hη : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-c) ≤ etaT (E N) (t N))
    (hLD : Step6LoopDecayPairN (sample d) E s t) :
    ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ σ : Fin 2 → Bool,
      FastDecay ((band d).L N) ((band d).ell N (s N) * ((band d).W N : ℝ) ^ τ)
        (((band d).W N : ℝ) ^ (-D)) (Step6.lkT (sample d) (E N) N (s N) σ) := by
  have hE : ∀ N, |E N| < 2 := fun N => by linarith [abs_nonneg (E N), hEκ N]
  obtain ⟨KM, hKM0, hM⟩ := exists_norm_lkPath_le_rpowN (sample d) hκ0 hκ1 hEκ hs0 ht1 hc0 hη
  refine fastDecay_lkT_of_pairN (sample d) hs0 hst ht1 hLD hKM0 hM ?_ ?_
  · intro N J
    exact (continuous_lkPath_gauss d N (hE N) ((hst N).trans_lt (ht1 N))
      J).aestronglyMeasurable
  · intro N J hJ hn
    exact integrable_sample_Lval (etaT_pos_of_lt_one (hE N) ((hst N).trans_lt (ht1 N)))
      (abs_im_zt (E N) (hE N) ((hst N).trans_lt (ht1 N))).ge J hJ hn

/-- **The (2.71) half of the step, Gaussian model**, at an `N`-dependent energy: `BoundsN` at `t`
from `BoundsN` at `s`, (2.68)–(2.70) at `t`, `Step6LoopDecayPairN` and the bounds on `Ξ^{(L-K)}`.
The proof uses `RBM.Gauss.bounds_step_gauss_windowN`, with `hcont_gauss`/`hintU1_gauss`/
`hintU2_gauss` in the diagonal shape `fun N₀ => hcont_gauss d (hE N₀) hs0 ht1` etc. that
`bounds_step_gauss_windowN` requires (not a new hypothesis). -/
theorem bounds_step_gauss_window_pairN (d : Dims) {E : ℕ → ℝ} {κ : ℝ} (hκ0 : 0 < κ)
    (hκ1 : κ ≤ 1) (hEκ : ∀ N, |E N| ≤ 2 - κ) {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hc : Cond272N (band d) E s t) {c : ℝ}
    (hc0 : 0 ≤ c)
    (hη : ∀ᶠ N : ℕ in atTop, ∀ u : TimeIcc s t N, (N : ℝ) ^ (-c) ≤ etaT (E N) u)
    (hLD : Step6LoopDecayPairN (sample d) E s t)
    (hxi1 : StochDom (band d).P (fun N u ω => Step3.flowXiLK (sample d) (E N) s t 1 N u ω)
      fun _ _ _ => (1 : ℝ))
    (hxi2 : StochDom (band d).P (fun N u ω => Step3.flowXiLK (sample d) (E N) s t 2 N u ω)
      fun _ _ _ => (1 : ℝ))
    (hxi3 : StochDom (band d).P (fun N u ω => Step3.flowXiLK (sample d) (E N) s t 3 N u ω)
      fun _ _ _ => (1 : ℝ))
    (hlmk : SharpLmKFlowN (sample d) E s t)
    (hBC : BoundsCoreN (sample d) E t) (hB : BoundsN (sample d) E s) :
    BoundsN (sample d) E t := by
  have hE : ∀ N, |E N| < 2 := fun N => by linarith [abs_nonneg (E N), hEκ N]
  have hηt : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-c) ≤ etaT (E N) (t N) := by
    filter_upwards [hη] with N hN
    exact hN ⟨t N, hst N, le_rfl⟩
  obtain ⟨KM, hKM0, hin59⟩ :=
    exists_fdInputs_highProb_pairN (sample d) hκ0 hκ1 hEκ hs0 ht1 hc0 hηt hLD
  exact bounds_step_gauss_windowN d hκ0 hκ1 hEκ hs0 hst ht1 hc hc0 hη
    (fun N₀ => hcont_gauss d (hE N₀) hs0 ht1) (fun N₀ => hintU1_gauss d (hE N₀) hs0 ht1)
    (fun N₀ => hintU2_gauss d (hE N₀) hs0 ht1)
    hKM0 (hlk_gauss_pairN d hκ0 hκ1 hEκ hs0 hst ht1 hc0 hηt hLD) hin59
    (highProb_quadInputs_pairN (sample d) hLD hxi2)
    (highProb_egInputs_pairN (sample d) hLD hxi1 hxi3)
    (loopDecay_Kval_quantN (band d) (fun N => (hE N).le) hs0 ht1 3) hlmk hBC hB

end RBM.Gauss
