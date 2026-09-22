/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellDriftRaw
import RBM1D.Gauss.APrimeDriftTimeFamily
import RBM1D.Gauss.Lemma514FpathZero

/-!
# Actual moving-endpoint raw drift transport (T431)

The actual full drift profile from T422 is transported from every real `r ∈ [0,u_k]` to the
literal moving endpoint `u_k`.  The running loop maximum and the `W⁻⁶⁰` floor remain unabsorbed.
-/

namespace RBM.APrimeFirstCellDriftTransportRaw

open Filter MeasureTheory Gauss CutHypTheta
open scoped Matrix.Norms.L2Operator

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

/-- The scalar coefficient in T422 before its common `T_{r,60}` factor. -/
noncomputable def rawDriftCoeff (ν : ℝ) (N : ℕ) (r : ℝ) (ω : Ω d) : ℝ :=
  (N : ℝ) ^ ν * (etaT 0 r)⁻¹ *
      (B.ell N r / B.ell N 0) ^ 3 +
    Real.exp 1 * (Step2.jS (sample d) 0 60 N r ω) ^ 2 *
      (36 * ((etaT 0 r)⁻¹ *
        (((B.W N : ℝ) * B.ell N r * etaT 0 r)⁻¹)) +
        (B.W N : ℝ) * (B.L N : ℝ) *
          (B.W N : ℝ) ^ (-(60 : ℝ)))

/-- The exact normalized transport multiplier `Ξ_N R_v⁻² x_r⁻²`. -/
noncomputable def transportFactor (N : ℕ) (r v : ℝ) : ℝ :=
  Step2.xiK (B.L N) (B.W N) 1 *
    ((etaT 0 0 / etaT 0 v)⁻¹) ^ 2 *
    ((etaT 0 0 / etaT 0 r)⁻¹) ^ 2

/-- The transported T422 profile, with its loop `J²` and `W⁻⁶⁰` floor unchanged. -/
noncomputable def transportedRawProfile
    (ν : ℝ) (N : ℕ) (r v : ℝ) (ω : Ω d) : ℝ :=
  transportFactor N r v * rawDriftCoeff ν N r ω

/-- T422's indexed profile is exactly a scalar coefficient times the common flow tail. -/
theorem driftProfile_eq_rawDriftCoeff_mul_tT
    (ν : ℝ) (N : ℕ) (r : ℝ) (ω : Ω d)
    (a₁ a₂ : ZMod (B.L N)) :
    APrimeFirstCellDriftRaw.driftProfile ν N r ω a₁ a₂ =
      rawDriftCoeff ν N r ω *
        Step2.tT B 0 N 60 r (zdist (B.L N) (a₁ - a₂)) := by
  have hdist : zdist (B.L N) (a₂ - a₁) = zdist (B.L N) (a₁ - a₂) := by
    rw [← zdist_neg (B.L N) (a₁ - a₂), neg_sub]
  simp only [APrimeFirstCellDriftRaw.driftProfile,
    APrimeFirstCellDriftRaw.eGpmProfile,
    APrimeFirstCellDriftRaw.quadProfile, rawDriftCoeff, Step2.tT, hdist]
  ring

private theorem normalized_transport_identity
    {M Ξ T η₀ ηr ηv : ℝ}
    (hT : T ≠ 0) (hη₀ : η₀ ≠ 0) (hηr : ηr ≠ 0) (hηv : ηv ≠ 0) :
    (M * (ηr / ηv) ^ 2 * Ξ * T) / (T * (η₀ / ηv) ^ 4) =
      Ξ * ((η₀ / ηv)⁻¹) ^ 2 * ((η₀ / ηr)⁻¹) ^ 2 * M := by
  field_simp

/-- Deterministic moving-endpoint transport of the full raw coefficient. -/
theorem driftAt_le_transportedRawProfile_of_raw
    (ν : ℝ) (N : ℕ) (r v : ℝ) (ω : Ω d)
    (a : LoopArg (d.L N) 2)
    (hv : v ∈ Set.Icc (0 : ℝ) (1 / 2)) (hr : r ∈ Set.Icc (0 : ℝ) v)
    (hW : Real.exp 1 ≤ (d.W N : ℝ))
    (hraw : ∀ b : LoopArg (d.L N) 2,
      ‖DriftDef.driftF B 0 N r ((sample d).H N r ω) Step2.sigPM b‖ ≤
        rawDriftCoeff ν N r ω *
          Step2.tT B 0 N 60 r (zdist (d.L N) (b 0 - b 1))) :
    APrimeDriftTimeFamily.driftAt d 0 60 N Step2.sigPM a 0 v r ω ≤
      transportedRawProfile ν N r v ω := by
  have hv1 : v < 1 := hv.2.trans_lt (by norm_num)
  have hr1 : r < 1 := hr.2.trans_lt hv1
  have hη₀ : 0 < etaT 0 0 := Step2.etaT_pos' (by norm_num) (by norm_num)
  have hηr : 0 < etaT 0 r := Step2.etaT_pos' (by norm_num) hr1
  have hηv : 0 < etaT 0 v := Step2.etaT_pos' (by norm_num) hv1
  have hℓr : 0 < B.ell N r := by
    exact lt_of_lt_of_le zero_lt_one
      (one_le_ellHat_of_nonneg (B.one_le_L N) hr.1 hr1)
  have hℓ₀ : 0 < B.ell N 0 := by
    exact lt_of_lt_of_le zero_lt_one
      (one_le_ellHat_of_nonneg (B.one_le_L N) (by norm_num) (by norm_num))
  have hM : 0 ≤ rawDriftCoeff ν N r ω := by
    unfold rawDriftCoeff
    positivity
  have hU := Step2.norm_Uker_flow (B := B) (E := 0) (D := 60)
    (by norm_num : |(0 : ℝ)| < 2) hr.1 hr.2 hv.1 hv1 hW hM hraw a
  have hscale : 0 < APrimeDriftTimeFamily.driftScale d 0 60 N a 0 v :=
    APrimeDriftTimeFamily.driftScale_pos d (D := 60)
      (by norm_num) hv.1 hv1 N a
  have hT : 0 < Step2.tT B 0 N 60 v (zdist (d.L N) (a 0 - a 1)) := by
    unfold Step2.tT
    exact tailT_pos (by exact_mod_cast d.W_pos N) _
  rw [APrimeDriftTimeFamily.driftAt]
  calc
    ‖Uker (d.L N) (xiOf (mSigma 0) Step2.sigPM) (r : ℂ) (v : ℂ)
        (DriftDef.driftF B 0 N r ((sample d).H N r ω) Step2.sigPM) a‖ /
          APrimeDriftTimeFamily.driftScale d 0 60 N a 0 v ≤
        (rawDriftCoeff ν N r ω * (etaT 0 r / etaT 0 v) ^ 2 *
          Step2.xiK (B.L N) (B.W N) (mE 0).im *
          Step2.tT B 0 N 60 v (zdist (d.L N) (a 0 - a 1))) /
            APrimeDriftTimeFamily.driftScale d 0 60 N a 0 v :=
      div_le_div_of_nonneg_right hU hscale.le
    _ = transportedRawProfile ν N r v ω := by
      rw [show (mE 0).im = 1 by norm_num [mE_zero]]
      unfold APrimeDriftTimeFamily.driftScale transportedRawProfile transportFactor
      exact normalized_transport_identity hT.ne' hη₀.ne' hηr.ne' hηv.ne'

/-- The exact T422 event-level raw drift after transport to the moving endpoint `v=u_k`. -/
def rawTransportBound (τ' δ ν : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop,
    ∀ ω ∈ APrimeFirstCellEGAllOutputRunning.good τ' δ ν N,
    ∀ N0 p k m : ℕ, N0 ≤ N → 1 ≤ p → 1 ≤ m →
      1 ≤ k → k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
        APrimeSmoothTransition.transitionMesh N →
      0 < APrimeSupportRunning.weight δ (firstCellT τ')
        N0 p N k m ω →
      let v := cutNetPt (fun _ => 0)
        APrimeSmoothTransition.transitionMesh N k
      ∀ r ∈ Set.Icc (0 : ℝ) v, ∀ a : LoopArg (d.L N) 2,
        APrimeDriftTimeFamily.driftAt d 0 60 N Step2.sigPM a 0 v r ω ≤
          transportedRawProfile ν N r v ω

/-- The actual T422 raw drift is transported for every real time in the closed running interval. -/
theorem eventually_raw_transport_on_active_support {τ' δ ν : ℝ}
    (hτ' : 0 < τ') (hδ : 0 < δ) (hδ100 : δ ≤ 1 / 100)
    (hν : 0 < ν) : rawTransportBound τ' δ ν := by
  filter_upwards [
    APrimeFirstCellDriftRaw.eventually_raw_drift_on_active_support
      hτ' hδ hδ100 hν,
    B.eventually_le_W (Real.exp 1)] with N hraw hW
  intro ω hω N0 p k m hN0 hp hm hk hkT hw
  dsimp only
  let v := cutNetPt (fun _ => 0)
    APrimeSmoothTransition.transitionMesh N k
  have hwin : (0 : ℝ) ≤ firstCellT τ' N :=
    (APrimeSupportRunning.firstT_bounds hτ' N).1
  have hvTop := MomentDuhamelCut.netFinset_subset_Icc hwin
    (APrimeSupportRunning.mesh_pos N) v (cutNetPt_mem_netFinset hkT)
  have hv : v ∈ Set.Icc (0 : ℝ) (1 / 2) :=
    ⟨hvTop.1, hvTop.2.trans (APrimeSupportRunning.firstT_bounds hτ' N).2⟩
  intro r hr a
  apply driftAt_le_transportedRawProfile_of_raw ν N r v ω a hv hr hW
  intro b
  have hb := hraw ω hω N0 p k m hN0 hp hm hk hkT hw r hr (b 0) (b 1)
  have hb' :
      ‖DriftDef.driftF B 0 N r ((sample d).H N r ω)
        Step2.sigPM ![b 0, b 1]‖ ≤
          APrimeFirstCellDriftRaw.driftProfile ν N r ω (b 0) (b 1) := by
    simpa only [show (![true, false] : Fin 2 → Bool) = Step2.sigPM from rfl] using hb
  have hbvec : (![b 0, b 1] : LoopArg (d.L N) 2) = b :=
    Step2FarInputs.etaExpand_two b
  have hb'' :
      ‖DriftDef.driftF B 0 N r ((sample d).H N r ω) Step2.sigPM b‖ ≤
        APrimeFirstCellDriftRaw.driftProfile ν N r ω (b 0) (b 1) := by
    rw [← hbvec]
    exact hb'
  calc
    ‖DriftDef.driftF B 0 N r ((sample d).H N r ω) Step2.sigPM b‖ ≤
        APrimeFirstCellDriftRaw.driftProfile ν N r ω (b 0) (b 1) := hb''
    _ = rawDriftCoeff ν N r ω *
        Step2.tT B 0 N 60 r (zdist (d.L N) (b 0 - b 1)) :=
      driftProfile_eq_rawDriftCoeff_mul_tT ν N r ω (b 0) (b 1)

/-- The closed running interval includes both `r=0` and `r=v`. -/
theorem raw_transport_endpoints_of_bound {τ' δ ν : ℝ}
    (h : rawTransportBound τ' δ ν) :
    ∀ᶠ N : ℕ in atTop,
      ∀ ω ∈ APrimeFirstCellEGAllOutputRunning.good τ' δ ν N,
      ∀ N0 p k m : ℕ, N0 ≤ N → 1 ≤ p → 1 ≤ m →
        1 ≤ k → k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
          APrimeSmoothTransition.transitionMesh N →
        0 < APrimeSupportRunning.weight δ (firstCellT τ')
          N0 p N k m ω →
        let v := cutNetPt (fun _ => 0)
          APrimeSmoothTransition.transitionMesh N k
        ∀ a : LoopArg (d.L N) 2,
          (APrimeDriftTimeFamily.driftAt d 0 60 N Step2.sigPM a 0 v 0 ω ≤
              transportedRawProfile ν N 0 v ω) ∧
            (APrimeDriftTimeFamily.driftAt d 0 60 N Step2.sigPM a 0 v v ω ≤
              transportedRawProfile ν N v v ω) := by
  filter_upwards [h] with N hN
  intro ω hω N0 p k m hN0 hp hm hk hkT hw
  dsimp only
  let v := cutNetPt (fun _ => 0)
    APrimeSmoothTransition.transitionMesh N k
  have hv0 : 0 ≤ v := by
    simp only [v, cutNetPt, zero_add]
    exact div_nonneg (Nat.cast_nonneg k)
      (APrimeSupportRunning.mesh_pos N).le
  intro a
  exact ⟨hN ω hω N0 p k m hN0 hp hm hk hkT hw 0 ⟨le_rfl, hv0⟩ a,
    hN ω hω N0 p k m hN0 hp hm hk hkT hw v ⟨hv0, le_rfl⟩ a⟩

/-- The `k=0` first-cell branch is exactly zero before any transport estimate is needed. -/
theorem driftAt_zero_window (N : ℕ) (ω : Ω d) (a : LoopArg (d.L N) 2) :
    APrimeDriftTimeFamily.driftAt d 0 60 N Step2.sigPM a 0 0 0 ω = 0 := by
  let F : LoopArg (d.L N) 2 → ℂ := fun b =>
    DriftDef.driftF B 0 N 0 ((sample d).H N 0 ω) Step2.sigPM b
  have hF : F = 0 := by
    funext b
    have hzero :=
      Gauss.driftF_zero_at_initial (E := 0) (sample d)
        (by norm_num) N 0 ω Step2.sigPM b
    change DriftDef.driftF B 0 N 0 ((sample d).H N 0 ω) Step2.sigPM b = 0 at hzero
    exact hzero
  have hU :
      Uker (d.L N) (xiOf (mSigma 0) Step2.sigPM) (0 : ℂ) (0 : ℂ) F a = 0 := by
    rw [hF]
    exact congrFun
      (FastDecayFlow.Uker_zero (L := d.L N)
        (xiOf (mSigma 0) Step2.sigPM) (0 : ℂ) (0 : ℂ)) a
  change ‖Uker (d.L N) (xiOf (mSigma 0) Step2.sigPM) (0 : ℂ) (0 : ℂ) F a‖ /
      APrimeDriftTimeFamily.driftScale d 0 60 N a 0 0 = 0
  rw [hU, norm_zero, zero_div]

theorem driftAt_cutNet_zero (N : ℕ) (ω : Ω d) (a : LoopArg (d.L N) 2) :
    APrimeDriftTimeFamily.driftAt d 0 60 N Step2.sigPM a 0
      (cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N 0) 0 ω = 0 := by
  simpa only [cutNetPt_zero] using driftAt_zero_window N ω a

/-- A positive `k=2` resident on T422's same literal event after deterministic transport. -/
def positiveRawTransportPlateau (τ' δ ν : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop,
    ∃ ω ∈ APrimeFirstCellEGAllOutputRunning.good τ' δ ν N,
    2 ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N ∧
    (∀ p : ℕ, APrimeSupportRunning.weight δ (firstCellT τ')
      2 p N 2 N ω = 1) ∧
    (∀ p : ℕ, APrimeSupportRunning.weight (1 / 100) (firstCellT τ')
      2 p N 2 N ω = 1) ∧
    let u2 := cutNetPt (fun _ => 0)
      APrimeSmoothTransition.transitionMesh N 2
    0 < u2 ∧ u2 ≤ firstCellT τ' N ∧
    ∀ a : LoopArg (d.L N) 2,
      APrimeDriftTimeFamily.driftAt d 0 60 N Step2.sigPM a 0 u2 u2 ω ≤
        transportedRawProfile ν N u2 u2 ω

theorem positiveRawTransportPlateau_of_raw {τ' δ ν : ℝ}
    (hτ' : 0 < τ') (hδ : 0 < δ) (hδ100 : δ ≤ 1 / 100)
    (hν : 0 < ν) (hplat : APrimeFirstCellDriftRaw.positiveRawDriftPlateau τ' δ ν) :
    positiveRawTransportPlateau τ' δ ν := by
  filter_upwards [hplat,
    eventually_raw_transport_on_active_support hτ' hδ hδ100 hν,
    eventually_ge_atTop 2] with N hplat htrans hN
  obtain ⟨ω, hω, hk, hwδ, hw100, hu2pos, hu2le, _hraw⟩ := hplat
  let u2 := cutNetPt (fun _ => 0)
    APrimeSmoothTransition.transitionMesh N 2
  have ht := htrans ω hω 2 1 2 N (by omega) (by norm_num) (by omega)
    (by norm_num) hk (by rw [hwδ 1]; norm_num)
  exact ⟨ω, hω, hk, hwδ, hw100, hu2pos, hu2le,
    fun a => ht u2 ⟨hu2pos.le, le_rfl⟩ a⟩

#print axioms driftProfile_eq_rawDriftCoeff_mul_tT
#print axioms driftAt_le_transportedRawProfile_of_raw
#print axioms eventually_raw_transport_on_active_support
#print axioms raw_transport_endpoints_of_bound
#print axioms driftAt_zero_window
#print axioms driftAt_cutNet_zero
#print axioms positiveRawTransportPlateau_of_raw

end

end RBM.APrimeFirstCellDriftTransportRaw
