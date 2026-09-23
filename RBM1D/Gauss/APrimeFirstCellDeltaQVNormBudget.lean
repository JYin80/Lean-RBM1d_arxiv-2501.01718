/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellQVWeightedGood
import RBM1D.Gauss.APrimeFirstCellCanonicalPlateau
import RBM1D.Gauss.APrimeFirstCellDeltaFarRowAbsorb
import RBM1D.Gauss.APrimeFirstCellDriftNormSplit
import RBM1D.Gauss.APrimeFirstCellSampleRegularity
import RBM1D.Gauss.APrimeFirstCellTimeIntegrability
import RBM1D.Gauss.APrimeQVGlobalPoly
import RBM1D.Gauss.APrimeFirstCellFullCrossBudget

/-!
# T545: variable-delta canonical QV norm and integral budget

This file pays the complement of the literal sharp common event in the
canonical weighted `L^p` norm of the actual, uncut first-cell QV.  It also
integrates the resulting moving-endpoint rate.
-/

namespace RBM.APrimeFirstCellDeltaQVNormBudget

open Filter MeasureTheory Set Gauss CutHypTheta

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

noncomputable def endpoint (N k : ℕ) : ℝ :=
  cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k

noncomputable def weight (τ' delta : ℝ) (p N k : ℕ) : Ω d → ℝ :=
  APrimeFirstCellCanonicalPlateau.canonicalWeight τ' delta p N k

noncomputable def qv (N k : ℕ) (a : LoopArg (d.L N) 2)
    (r : ℝ) : Ω d → ℝ :=
  APrimeFirstCellSampleRegularity.Q N k a r

noncomputable def g (τ' delta : ℝ) (p N k : ℕ)
    (a : LoopArg (d.L N) 2) (r : ℝ) : ℝ :=
  APrimeModel.rateNormW (P d) (weight τ' delta p N k) p (qv N k a r)

noncomputable def qvEnvelope (N : ℕ) : ℝ :=
  2 ^ (21 : ℕ) * (N : ℝ) ^ (136 : ℝ)

/-- The global polynomial estimate specializes to the actual first-cell QV,
uniformly over every active endpoint and both closed time endpoints. -/
theorem eventually_abs_qv_le_envelope {τ' : ℝ} (hτ' : 0 < τ') :
    ∀ᶠ N : ℕ in atTop, ∀ k : ℕ,
      k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
        APrimeSmoothTransition.transitionMesh N →
      ∀ r ∈ Icc (0 : ℝ) (endpoint N k),
      ∀ a : LoopArg (d.L N) 2, ∀ ω : Ω d,
        |qv N k a r ω| ≤ qvEnvelope N := by
  filter_upwards [
    APrimeQVGlobalPoly.eventually_qvAt_le_poly d
      (E := 0) (D := 60) (Kη := 1) (by norm_num) (by norm_num) (by norm_num),
    eventually_ge_atTop 2] with N hpoly hN
  intro k hk r hr a ω
  have ht := APrimeSupportRunning.firstT_bounds hτ' N
  have hv : endpoint N k ∈ Icc (0 : ℝ) (firstCellT τ' N) := by
    exact MomentDuhamelCut.netFinset_subset_Icc ht.1
      (APrimeSupportRunning.mesh_pos N) _ (cutNetPt_mem_netFinset hk)
  have hv1 : endpoint N k < 1 :=
    hv.2.trans ht.2 |>.trans_lt (by norm_num)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hfloor : (N : ℝ) ^ (-(1 : ℝ)) ≤ etaT 0 (endpoint N k) := by
    rw [Real.rpow_neg_one]
    simp only [etaT, mE_zero, Complex.I_im, mul_one]
    have hNc : (2 : ℝ) ≤ N := by exact_mod_cast hN
    calc
      (N : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hNc
      _ = 1 / 2 := by norm_num
      _ ≤ 1 - endpoint N k := by linarith [hv.2, ht.2]
  have hq := hpoly 0 (endpoint N k) (by norm_num) hv.1 hv1 hfloor
    Step2.sigPM a r hr ω
  change |APrimeDriftTimeFamily.qvAt d 0 60 N Step2.sigPM a 0
    (endpoint N k) r ω| ≤ qvEnvelope N
  rw [abs_of_nonneg hq.1]
  unfold qvEnvelope
  convert hq.2 using 1 <;> norm_num

theorem eventually_qvEnvelope_le_rpow :
    ∀ᶠ N : ℕ in atTop, qvEnvelope N ≤ (N : ℝ) ^ (137 : ℝ) := by
  filter_upwards [eventually_ge_atTop (2 ^ (21 : ℕ))] with N hN
  have hNc : (2 : ℝ) ^ (21 : ℕ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hNpos : (0 : ℝ) < N := by
    exact_mod_cast (show 0 < N by omega)
  unfold qvEnvelope
  calc
    2 ^ (21 : ℕ) * (N : ℝ) ^ (136 : ℝ)
        ≤ (N : ℝ) * (N : ℝ) ^ (136 : ℝ) :=
      mul_le_mul_of_nonneg_right hNc (Real.rpow_nonneg hN0 _)
    _ = (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (136 : ℝ) := by
      rw [Real.rpow_one]
    _ = (N : ℝ) ^ ((1 : ℝ) + 136) :=
      (Real.rpow_add hNpos 1 136).symm
    _ = (N : ℝ) ^ (137 : ℝ) := by norm_num

/-- The exact eventual moving-endpoint norm statement.  The moment order and
the requested decay exponent are fixed before the eventual size cutoff. -/
def actualQVNormBudget (τ' delta α : ℝ) (p : ℕ) (β : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∀ k : ℕ, 1 ≤ k →
    k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N →
    let v := endpoint N k
    ∀ r ∈ Icc (0 : ℝ) v, ∀ a : LoopArg (d.L N) 2,
      g τ' delta p N k a r ≤
        APrimeFirstCellQVCurrentRows.currentRate delta
          (APrimeFirstCellDeltaFarRowAbsorb.tau delta) α N v r +
          (N : ℝ) ^ (-β)

/-- T448 supplies the favorable weighted inequality; the all-sample
`2^21 N^136` envelope and high probability of that same event pay its
complement in the canonical weighted `L^p` norm. -/
theorem eventually_actualQVNormBudget_of_highProb {τ' delta α : ℝ}
    (hτ' : 0 < τ') (hdelta : 0 < delta) (hα : 0 < α)
    {p : ℕ} (hp : 1 ≤ p)
    {β : ℝ} (hβ : 0 < β)
    (hΞ : HighProb (P d)
      (APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' delta α)) :
    actualQVNormBudget τ' delta α p β := by
  have hpay := Gauss.eventually_env_mul_prob_rpow_le (P := P d)
    (q := p) (by omega) hΞ (Env := qvEnvelope) (Cenv := 137)
    (by norm_num) eventually_qvEnvelope_le_rpow hβ
  filter_upwards [
    APrimeFirstCellQVWeightedGood.weightedCurrentRowsGood_of_currentRows
      (APrimeFirstCellQVCurrentRows.eventually_currentRowsBound
        hτ' hdelta.le hα),
    eventually_abs_qv_le_envelope hτ', hpay,
    eventually_ge_atTop 2] with N hgood henv hpayN hN
  intro k hk1 hk
  let v := endpoint N k
  let m := APrimeSmoothWeightActual.canonicalM d (fun _ => 0)
    (firstCellT τ') APrimeSmoothTransition.transitionMesh N
  have hm : 1 ≤ m := APrimeSmoothWeightActual.canonicalM_pos d (fun _ => 0)
    (firstCellT τ') APrimeSmoothTransition.transitionMesh N
  have ht := APrimeSupportRunning.firstT_bounds hτ' N
  have hv : v ∈ Icc (0 : ℝ) (firstCellT τ' N) := by
    exact MomentDuhamelCut.netFinset_subset_Icc ht.1
      (APrimeSupportRunning.mesh_pos N) _ (cutNetPt_mem_netFinset hk)
  have hvhalf : v ≤ 1 / 2 := hv.2.trans ht.2
  have hw0 : ∀ ω, 0 ≤ weight τ' delta p N k ω := by
    intro ω
    exact APrimeSmoothWeightActual.weight_nonneg d 0 60 delta (fun _ => 0)
      (firstCellT τ') APrimeSmoothTransition.transitionMesh
      2 p N k m ω
  have hw1 : ∀ ω, weight τ' delta p N k ω ≤ 1 := by
    intro ω
    exact APrimeSmoothWeightActual.weight_le_one d 0 60 delta (fun _ => 0)
      (firstCellT τ') APrimeSmoothTransition.transitionMesh
      2 p N k m ω
  dsimp only
  intro r hr a
  have hreg := APrimeFirstCellSampleRegularity.actual_generator_sampleRegularity
    (δ := delta) hτ' hp (show 0 < N by omega) hk a hr
  have hrate0 : 0 ≤ APrimeFirstCellQVCurrentRows.currentRate
      delta (APrimeFirstCellDeltaFarRowAbsorb.tau delta) α N v r := by
    exact APrimeFirstCellFullCrossIntegrability.currentRate_nonneg
      (show 1 ≤ N by omega) hv.1 hvhalf hr
  have hEnv0 : 0 ≤ qvEnvelope N := by unfold qvEnvelope; positivity
  have hsplit := APrimeFirstCellDriftNormSplit.weighted_norm_le_of_weighted_event
    (P0 := P d) (q := p) (by omega) hw0 hw1 hreg.hQi
    (APrimeFirstCellSharpCommonEvent.measurableSet_sharpCommonEvent hτ' delta α N)
    hrate0 hEnv0 ENNReal.toReal_nonneg
    (fun ω hω => by
      have hrow := hgood ω hω 2 p k m hN hp hm hk1 hk r hr a
      have hq0 : 0 ≤ APrimeDriftTimeFamily.qvAt d 0 60 N
          Step2.sigPM a 0 (endpoint N k) r ω := by
        exact Gauss.quadVar_nonneg _ _
      change weight τ' delta p N k ω *
          |APrimeDriftTimeFamily.qvAt d 0 60 N Step2.sigPM a 0
            (endpoint N k) r ω| ≤
        weight τ' delta p N k ω *
          APrimeFirstCellQVCurrentRows.currentRate delta
            (APrimeFirstCellDeltaFarRowAbsorb.tau delta) α N v r
      rw [abs_of_nonneg hq0]
      convert hrow using 1 <;> rfl)
    (fun ω => henv k hk r hr a ω)
    (le_rfl : ((P d)
      (APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' delta α N)ᶜ).toReal ≤ _)
  change g τ' delta p N k a r ≤ _
  calc
    g τ' delta p N k a r ≤
        APrimeFirstCellQVCurrentRows.currentRate delta
          (APrimeFirstCellDeltaFarRowAbsorb.tau delta) α N v r +
          qvEnvelope N *
            (((P d)
              (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
                τ' delta α N)ᶜ).toReal) ^ ((1 : ℝ) / p) := by
      simpa [g, qv, APrimeModel.rateNormW, one_div] using hsplit
    _ ≤ APrimeFirstCellQVCurrentRows.currentRate delta
          (APrimeFirstCellDeltaFarRowAbsorb.tau delta) α N v r +
          (N : ℝ) ^ (-β) := add_le_add le_rfl hpayN

/-- On the first half-cell, the absorbed three-row current rate is bounded
by a constant in the time variable. -/
theorem currentRate_le_constant {delta α : ℝ} {N : ℕ} {v r : ℝ}
    (hN : 1 ≤ N) (hv0 : 0 ≤ v) (hvhalf : v ≤ 1 / 2)
    (hr : r ∈ Icc (0 : ℝ) v)
    (hbracket : APrimeFirstCellDeltaFarRowAbsorb.currentBracket
      delta N v r ≤ 3) :
    APrimeFirstCellQVCurrentRows.currentRate delta
      (APrimeFirstCellDeltaFarRowAbsorb.tau delta) α N v r ≤
      884736 * (N : ℝ) ^ α *
        APrimeFirstCellLoopCap.xRate v ^ (-(4 : ℝ)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hr1 : r < 1 := hr.2.trans hvhalf |>.trans_lt (by norm_num)
  have hv1 : v < 1 := hvhalf.trans_lt (by norm_num)
  have hηr : 0 < etaT 0 r := Step2.etaT_pos' (by norm_num) hr1
  have hxv : 0 < APrimeFirstCellLoopCap.xRate v := by
    unfold APrimeFirstCellLoopCap.xRate
    exact div_pos (Step2.etaT_pos' (by norm_num) (by norm_num))
      (Step2.etaT_pos' (by norm_num) hv1)
  have hηhalf : (1 / 2 : ℝ) ≤ etaT 0 r := by
    simp only [etaT, mE_zero, Complex.I_im, mul_one]
    linarith [hr.2, hvhalf]
  have hηinv : (etaT 0 r)⁻¹ ≤ (2 : ℝ) := by
    calc
      (etaT 0 r)⁻¹ ≤ ((1 / 2 : ℝ))⁻¹ :=
        inv_anti₀ (by norm_num) hηhalf
      _ = 2 := by norm_num
  have hpref0 : 0 ≤
      APrimeFirstCellQVCurrentRows.currentConstant * (N : ℝ) ^ α *
        (etaT 0 r)⁻¹ *
          APrimeFirstCellLoopCap.xRate v ^ (-(4 : ℝ)) := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg APrimeFirstCellQVCurrentRows.currentConstant_pos.le
          (Real.rpow_nonneg hNr.le _))
        (inv_nonneg.mpr hηr.le))
      (Real.rpow_nonneg hxv.le _)
  have hbase0 : 0 ≤
      APrimeFirstCellQVCurrentRows.currentConstant * (N : ℝ) ^ α *
        APrimeFirstCellLoopCap.xRate v ^ (-(4 : ℝ)) * 3 := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg APrimeFirstCellQVCurrentRows.currentConstant_pos.le
          (Real.rpow_nonneg hNr.le _))
        (Real.rpow_nonneg hxv.le _)) (by norm_num)
  calc
    APrimeFirstCellQVCurrentRows.currentRate delta
        (APrimeFirstCellDeltaFarRowAbsorb.tau delta) α N v r =
        APrimeFirstCellQVCurrentRows.currentConstant * (N : ℝ) ^ α *
          (etaT 0 r)⁻¹ *
            APrimeFirstCellLoopCap.xRate v ^ (-(4 : ℝ)) *
              APrimeFirstCellDeltaFarRowAbsorb.currentBracket delta N v r :=
      APrimeFirstCellDeltaFarRowAbsorb.currentRate_eq delta α N v r
    _ ≤ APrimeFirstCellQVCurrentRows.currentConstant * (N : ℝ) ^ α *
          (etaT 0 r)⁻¹ *
            APrimeFirstCellLoopCap.xRate v ^ (-(4 : ℝ)) * 3 :=
      mul_le_mul_of_nonneg_left hbracket hpref0
    _ = (APrimeFirstCellQVCurrentRows.currentConstant * (N : ℝ) ^ α *
          APrimeFirstCellLoopCap.xRate v ^ (-(4 : ℝ)) * 3) *
            (etaT 0 r)⁻¹ := by ring
    _ ≤ (APrimeFirstCellQVCurrentRows.currentConstant * (N : ℝ) ^ α *
          APrimeFirstCellLoopCap.xRate v ^ (-(4 : ℝ)) * 3) * 2 :=
      mul_le_mul_of_nonneg_left hηinv hbase0
    _ = 884736 * (N : ℝ) ^ α *
          APrimeFirstCellLoopCap.xRate v ^ (-(4 : ℝ)) := by
      unfold APrimeFirstCellQVCurrentRows.currentConstant
      norm_num
      ring

def actualQVIntegralBudget (τ' delta α : ℝ) (p : ℕ) (β : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∀ k : ℕ, 1 ≤ k →
    k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N →
    let v := endpoint N k
    ∀ a : LoopArg (d.L N) 2,
      (∫ r in (0 : ℝ)..v, g τ' delta p N k a r) ≤
        442368 * (N : ℝ) ^ α *
            APrimeFirstCellLoopCap.xRate v ^ (-(4 : ℝ)) +
          v * (N : ℝ) ^ (-β)

theorem eventually_actualQVIntegralBudget
    {τ' delta α β : ℝ} (hτ' : 0 < τ')
    (hdelta : 0 < delta) (hdelta100 : delta ≤ 1 / 100)
    (hβ : 0 < β)
    {p : ℕ} (_hp : 1 ≤ p)
    (hnorm : actualQVNormBudget τ' delta α p β) :
    actualQVIntegralBudget τ' delta α p β := by
  filter_upwards [hnorm,
    APrimeFirstCellDeltaFarRowAbsorb.eventually_currentBracket_le_three
      hτ' hdelta hdelta100,
    eventually_ge_atTop 1] with N hnormN hbracket hN
  intro k hk1 hk
  let v := endpoint N k
  have ht := APrimeSupportRunning.firstT_bounds hτ' N
  have hv : v ∈ Icc (0 : ℝ) (firstCellT τ' N) := by
    exact MomentDuhamelCut.netFinset_subset_Icc ht.1
      (APrimeSupportRunning.mesh_pos N) _ (cutNetPt_mem_netFinset hk)
  have hvhalf : v ≤ 1 / 2 := hv.2.trans ht.2
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hxv : 0 < APrimeFirstCellLoopCap.xRate v := by
    unfold APrimeFirstCellLoopCap.xRate
    exact div_pos (Step2.etaT_pos' (by norm_num) (by norm_num))
      (Step2.etaT_pos' (by norm_num) (hvhalf.trans_lt (by norm_num)))
  dsimp only
  intro a
  have hpoint : ∀ r ∈ Icc (0 : ℝ) v,
      g τ' delta p N k a r ≤
        884736 * (N : ℝ) ^ α *
            APrimeFirstCellLoopCap.xRate v ^ (-(4 : ℝ)) +
          (N : ℝ) ^ (-β) := by
    intro r hr
    calc
      g τ' delta p N k a r ≤
          APrimeFirstCellQVCurrentRows.currentRate delta
            (APrimeFirstCellDeltaFarRowAbsorb.tau delta) α N v r +
            (N : ℝ) ^ (-β) := by
        exact hnormN k hk1 hk r hr a
      _ ≤ 884736 * (N : ℝ) ^ α *
              APrimeFirstCellLoopCap.xRate v ^ (-(4 : ℝ)) +
            (N : ℝ) ^ (-β) :=
        add_le_add
          (currentRate_le_constant hN hv.1 hvhalf hr (hbracket k hk r hr)) le_rfl
  have hM0 : 0 ≤ 884736 * (N : ℝ) ^ α *
          APrimeFirstCellLoopCap.xRate v ^ (-(4 : ℝ)) +
        (N : ℝ) ^ (-β) := by positivity
  have hint := intervalIntegral_le_of_le_const hv.1 hM0 hpoint
  have hscale0 : 0 ≤ 884736 * (N : ℝ) ^ α *
      APrimeFirstCellLoopCap.xRate v ^ (-(4 : ℝ)) := by positivity
  calc
    (∫ r in (0 : ℝ)..v, g τ' delta p N k a r) ≤
        v * (884736 * (N : ℝ) ^ α *
              APrimeFirstCellLoopCap.xRate v ^ (-(4 : ℝ)) +
            (N : ℝ) ^ (-β)) := by simpa using hint
    _ = v * (884736 * (N : ℝ) ^ α *
            APrimeFirstCellLoopCap.xRate v ^ (-(4 : ℝ))) +
          v * (N : ℝ) ^ (-β) := by ring
    _ ≤ (1 / 2 : ℝ) * (884736 * (N : ℝ) ^ α *
            APrimeFirstCellLoopCap.xRate v ^ (-(4 : ℝ))) +
          v * (N : ℝ) ^ (-β) :=
      add_le_add (mul_le_mul_of_nonneg_right hvhalf hscale0) le_rfl
    _ = 442368 * (N : ℝ) ^ α *
            APrimeFirstCellLoopCap.xRate v ^ (-(4 : ℝ)) +
          v * (N : ℝ) ^ (-β) := by ring

/-- The square-root form used by the moment differential inequality. -/
def actualQVSqrtBudget (τ' delta α : ℝ) (p : ℕ) (β : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∀ k : ℕ, 1 ≤ k →
    k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N →
    let v := endpoint N k
    ∀ a : LoopArg (d.L N) 2,
      Real.sqrt (((2 : ℝ) * p - 1) *
        (∫ r in (0 : ℝ)..v, g τ' delta p N k a r)) ≤
      Real.sqrt (((2 : ℝ) * p - 1) *
        (442368 * (N : ℝ) ^ α *
            APrimeFirstCellLoopCap.xRate v ^ (-(4 : ℝ)) +
          v * (N : ℝ) ^ (-β)))

theorem eventually_actualQVSqrtBudget {τ' delta α β : ℝ} {p : ℕ}
    (hp : 1 ≤ p) (hint : actualQVIntegralBudget τ' delta α p β) :
    actualQVSqrtBudget τ' delta α p β := by
  have hcoef : 0 ≤ (2 : ℝ) * p - 1 := by
    have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  filter_upwards [hint] with N hintN
  intro k hk1 hk
  dsimp only
  intro a
  exact Real.sqrt_le_sqrt
    (mul_le_mul_of_nonneg_left (hintN k hk1 hk a) hcoef)

/-- The same square-root budget with the leading square evaluated. -/
def actualQVSqrtExplicitBudget (τ' delta α : ℝ) (p : ℕ) (β : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∀ k : ℕ, 1 ≤ k →
    k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N →
    let v := endpoint N k
    ∀ a : LoopArg (d.L N) 2,
      Real.sqrt (((2 : ℝ) * p - 1) *
        (∫ r in (0 : ℝ)..v, g τ' delta p N k a r)) ≤
      Real.sqrt ((2 : ℝ) * p - 1) *
        (384 * Real.sqrt 3 * (N : ℝ) ^ (α / 2) *
            APrimeFirstCellLoopCap.xRate v ^ (-(2 : ℝ)) +
          Real.sqrt v * (N : ℝ) ^ (-β / 2))

theorem eventually_actualQVSqrtExplicitBudget {τ' delta α β : ℝ} {p : ℕ}
    (hτ' : 0 < τ') (hp : 1 ≤ p)
    (hint : actualQVIntegralBudget τ' delta α p β) :
    actualQVSqrtExplicitBudget τ' delta α p β := by
  have hcoef : 0 ≤ (2 : ℝ) * p - 1 := by
    have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  filter_upwards [hint, eventually_ge_atTop 1] with N hintN hN
  intro k hk1 hk
  let v := endpoint N k
  have ht := APrimeSupportRunning.firstT_bounds hτ' N
  have hv : v ∈ Icc (0 : ℝ) (firstCellT τ' N) := by
    exact MomentDuhamelCut.netFinset_subset_Icc ht.1
      (APrimeSupportRunning.mesh_pos N) _ (cutNetPt_mem_netFinset hk)
  have hvhalf : v ≤ 1 / 2 := hv.2.trans ht.2
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hxv : 0 < APrimeFirstCellLoopCap.xRate v := by
    unfold APrimeFirstCellLoopCap.xRate
    exact div_pos (Step2.etaT_pos' (by norm_num) (by norm_num))
      (Step2.etaT_pos' (by norm_num) (hvhalf.trans_lt (by norm_num)))
  dsimp only
  intro a
  let A : ℝ := 442368 * (N : ℝ) ^ α *
    APrimeFirstCellLoopCap.xRate v ^ (-(4 : ℝ))
  let B : ℝ := v * (N : ℝ) ^ (-β)
  let X : ℝ := 384 * Real.sqrt 3 * (N : ℝ) ^ (α / 2) *
    APrimeFirstCellLoopCap.xRate v ^ (-(2 : ℝ))
  let Y : ℝ := Real.sqrt v * (N : ℝ) ^ (-β / 2)
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hB0 : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg hv.1 (Real.rpow_nonneg hNpos.le _)
  have hX0 : 0 ≤ X := by dsimp [X]; positivity
  have hY0 : 0 ≤ Y := by dsimp [Y]; positivity
  have hNhalf : ((N : ℝ) ^ (α / 2)) ^ 2 = (N : ℝ) ^ α := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
    congr 1
    ring
  have hxpow :
      (APrimeFirstCellLoopCap.xRate v ^ (-(2 : ℝ))) ^ 2 =
        APrimeFirstCellLoopCap.xRate v ^ (-(4 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hxv.le]
    congr 1
    ring
  have hXsq : X ^ 2 = A := by
    dsimp [X, A]
    calc
      (384 * √3 * (N : ℝ) ^ (α / 2) *
          APrimeFirstCellLoopCap.xRate v ^ (-(2 : ℝ))) ^ 2 =
        384 ^ 2 * (√3) ^ 2 * (((N : ℝ) ^ (α / 2)) ^ 2) *
          ((APrimeFirstCellLoopCap.xRate v ^ (-(2 : ℝ))) ^ 2) := by ring
      _ = _ := by
        rw [Real.sq_sqrt (by norm_num), hNhalf, hxpow]
        norm_num
  have hmain : Real.sqrt A = X := by
    rw [← hXsq, Real.sqrt_sq hX0]
  have herr : Real.sqrt B = Y := by
    dsimp [B, Y]
    rw [Real.sqrt_mul hv.1]
    congr 1
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hNpos.le]
    congr 1
    ring
  have hInt := hintN k hk1 hk a
  have hroot : Real.sqrt (((2 : ℝ) * p - 1) *
      (∫ r in (0 : ℝ)..v, g τ' delta p N k a r)) ≤
      Real.sqrt (((2 : ℝ) * p - 1) * (A + B)) := by
    apply Real.sqrt_le_sqrt
    exact mul_le_mul_of_nonneg_left (by simpa [A, B] using hInt) hcoef
  calc
    Real.sqrt (((2 : ℝ) * p - 1) *
        (∫ r in (0 : ℝ)..v, g τ' delta p N k a r)) ≤
        Real.sqrt (((2 : ℝ) * p - 1) * (A + B)) := hroot
    _ = Real.sqrt (((2 : ℝ) * p - 1) * A +
          ((2 : ℝ) * p - 1) * B) := by ring
    _ ≤ Real.sqrt (((2 : ℝ) * p - 1) * A) +
          Real.sqrt (((2 : ℝ) * p - 1) * B) :=
      sqrt_add_le_add_sqrt _ (mul_nonneg hcoef hB0)
    _ = Real.sqrt ((2 : ℝ) * p - 1) * Real.sqrt A +
          Real.sqrt ((2 : ℝ) * p - 1) * Real.sqrt B := by
      rw [Real.sqrt_mul hcoef, Real.sqrt_mul hcoef]
    _ = Real.sqrt ((2 : ℝ) * p - 1) * (X + Y) := by
      rw [hmain, herr]
      ring
    _ = Real.sqrt ((2 : ℝ) * p - 1) *
        (384 * Real.sqrt 3 * (N : ℝ) ^ (α / 2) *
            APrimeFirstCellLoopCap.xRate v ^ (-(2 : ℝ)) +
          Real.sqrt v * (N : ℝ) ^ (-β / 2)) := by rfl

@[simp] theorem endpoint_zero (N : ℕ) : endpoint N 0 = 0 := by
  simp only [endpoint, cutNetPt_zero]

/-- The geometric `k=0` branch has a zero time interval. -/
theorem integral_g_k_zero (τ' delta : ℝ) (p N : ℕ)
    (a : LoopArg (d.L N) 2) :
    (∫ r in (0 : ℝ)..endpoint N 0, g τ' delta p N 0 a r) = 0 := by
  rw [endpoint_zero, intervalIntegral.integral_same]

theorem sqrt_integral_g_k_zero (τ' delta : ℝ) (p N : ℕ)
    (a : LoopArg (d.L N) 2) :
    Real.sqrt (((2 : ℝ) * p - 1) *
      (∫ r in (0 : ℝ)..endpoint N 0, g τ' delta p N 0 a r)) = 0 := by
  rw [integral_g_k_zero]
  simp

/-- The positive `k=2` canonical resident and all three QV budgets coexist
with the literal sharp common event. -/
def positiveTwoSameEventBudget (τ' delta α : ℝ) (p : ℕ) (β : ℝ) : Prop :=
  APrimeFirstCellCanonicalPlateau.positiveCanonicalSharpPlateau
      τ' delta α ∧
    actualQVNormBudget τ' delta α p β ∧
    actualQVIntegralBudget τ' delta α p β ∧
    actualQVSqrtBudget τ' delta α p β ∧
    actualQVSqrtExplicitBudget τ' delta α p β

/-- Closed producer: one literal measurable high-probability event supports
the canonical norm estimate, its integrated and square-root budgets, the
zero branch, and a positive same-event `k=2` resident. -/
theorem exists_actualQVNormBudget_with_resident :
    ∃ τ' : ℝ, 0 < τ' ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ 1 / 100 →
      ∀ α : ℝ, 0 < α → ∀ p : ℕ, 1 ≤ p → ∀ β : ℝ, 0 < β →
        (∀ N, MeasurableSet
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
            τ' delta α N)) ∧
        HighProb (P d)
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent
            τ' delta α) ∧
        positiveTwoSameEventBudget τ' delta α p β := by
  obtain ⟨τ', hτ', hall⟩ :=
    APrimeFirstCellCanonicalPlateau.exists_sharpCommonEvent_with_canonical_plateau
  refine ⟨τ', hτ', ?_⟩
  intro delta hdelta hdelta100 α hα p hp β hβ
  obtain ⟨hmeas, hhigh, hresident⟩ :=
    hall delta hdelta hdelta100 α hα
  have hnorm := eventually_actualQVNormBudget_of_highProb
    hτ' hdelta hα hp hβ hhigh
  have hint := eventually_actualQVIntegralBudget
    hτ' hdelta hdelta100 hβ hp hnorm
  have hsqrt := eventually_actualQVSqrtBudget hp hint
  have hexplicit := eventually_actualQVSqrtExplicitBudget hτ' hp hint
  exact ⟨hmeas, hhigh, hresident, hnorm, hint, hsqrt, hexplicit⟩

#print axioms eventually_abs_qv_le_envelope
#print axioms eventually_qvEnvelope_le_rpow
#print axioms eventually_actualQVNormBudget_of_highProb
#print axioms currentRate_le_constant
#print axioms eventually_actualQVIntegralBudget
#print axioms eventually_actualQVSqrtBudget
#print axioms eventually_actualQVSqrtExplicitBudget
#print axioms endpoint_zero
#print axioms integral_g_k_zero
#print axioms sqrt_integral_g_k_zero
#print axioms exists_actualQVNormBudget_with_resident

end

end RBM.APrimeFirstCellDeltaQVNormBudget
