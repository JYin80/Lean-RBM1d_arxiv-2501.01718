/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Lemma514NonAltTwo
import RBM1D.Flow.EnergyUniform
import RBM1D.EnergyN.Gauss.Step2Plain
import RBM1D.EnergyN.Gauss.Lemma510Fixed
import RBM1D.EnergyN.Gauss.GridAssembly
import RBM1D.EnergyN.Gauss.Lemma514Moment
import RBM1D.EnergyN.Unif.Gauss.Lemma514NonAlt
import RBM1D.EnergyN.Gauss.Lemma514NonAlt

/-!
# The non-alternating endpoint case of Lemma 5.14 for loops of length two

At an `N`-dependent energy `E : ℕ → ℝ`: `Grid.assembly514_twoN`,
`Grid.endpoint_nonAlt_two_ite_plainN` and `Grid.endpoint_nonAlt_two_plainN`, the length-two case
of `EnergyN/Gauss/Lemma514NonAlt.lean`, with the same treatment of the constants.

## The energy-dependent constants, all at `endpoint_nonAlt_two_ite_plainN`

* `CK`: `Grid.exists_Kval_env_unif` (`RBM1D/EnergyN/Unif/Gauss/Lemma514NonAlt.lean`) gives `CK`
  uniform in `E`, so `hKenv` holds as stated, with no comparison.
* `cK`, `cK2`: fixed at the constant `√κ'` (`κ' := min κ 1`); `cKerShort n` is antitone in
  its real argument (private helper `cKerShort_anti` below, proved in this file since Lean
  `private` is file-local), and `min (2 - |E N|) 1 ≥ κ'` for every `N` (from `hEκ N`), so the
  `cK`-coefficient of the fixed-`κ'` facts `ha1/he2/he3` bounds the coefficient
  `cKerShort (…) (√(min (2-|E N|) 1))` needed at each `N`; a nonneg-factor comparison gives the
  fact at each `N` from the fixed one.
* `mi` in `ev_ha2`/`ev_ha3`: fixed at `mκ := √(2κ')/2` (`hmκpos`, independent of `E`/`N`),
  with `mκ ≤ (mE (E N)).im` for every `N` (`mE_im_ge`), so `(mE (E N)).im⁻¹ ≤ mκ⁻¹`
  (`inv_anti₀`), combined with the `cK` comparison above at every use of
  `ha1N/ha2N/ha3N/he2N/he3N` inside the final `budget514` call.
-/

noncomputable section

namespace RBM.Gauss.Grid

open MeasureTheory ProbabilityTheory Filter Matrix RBM
open scoped NNReal ENNReal Matrix.Norms.L2Operator

variable (d : Dims)

section Assembly514TwoN

set_option maxHeartbeats 8000000 in
theorem assembly514_twoN {E : ℕ → ℝ} (hE : ∀ N, |E N| < 2) (s v : ℕ → ℝ)
    (σ : Fin (2) → Bool) {k0 : Fin (2)} (hk0 : σ k0 = σ (k0 + 1))
    {ε₁ τ' D' D_Y D₁ C_P C_K : ℝ} (hε₁ : 0 < ε₁) (hτ' : 0 < τ') (hD' : 1 ≤ D')
    (hCK0 : 0 ≤ C_K) (hCK : D₁ + 4 * D_Y + ((2 : ℕ) : ℝ) * 1 + 2 * C_P + 8 ≤ C_K)
    {CK : ℝ} (hCK0' : 0 ≤ CK)
    (hKenv : ∀ (N : ℕ) (u : ℝ), 0 ≤ u → u < 1 → 1 ≤ (band d).scale (E N) N u →
      (∀ J : LoopIdx (ZMod (d.L N)), J.WF → 2 ≤ J.length → J.length ≤ 2 →
        ‖(band d).Kval (E N) N u J‖ ≤ CK * ((band d).scale (E N) N u)⁻¹ ^ (J.length - 1))
      ∧ ∀ J : LoopIdx (ZMod (d.L N)), J.WF → J.length ≤ 2 → ‖(band d).Kval (E N) N u J‖ ≤ CK + 1)
    (K : ℕ → ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ (Λ Φ ℓs : ℝ), 0 ≤ Λ → 0 ≤ Φ →
      0 ≤ s N → s N < v N → v N < 1 → 1 ≤ K N → K N ≤ ⌈(N : ℝ) ^ C_K⌉₊ →
      step s v K N ≤ (N : ℝ) ^ (-C_K) → (d.L N : ℝ) ≤ (N : ℝ) ^ (1 : ℝ) →
      (∀ u, 0 ≤ u → u ≤ v N → 1 ≤ (band d).scale (E N) N u) →
      KDecayRegime d N (2) τ' D' →
      PY514 d N (2) (v N) (etaT (E N) (v N)) ≤ (N : ℝ) ^ C_P →
      (∀ j < K N, (N : ℝ) ^ ε₁ * Λ
        + ((2 * (2) + 2 : ℕ) : ℝ) * ((etaT (E N) (time s v K N (j + 1)))⁻¹ ^ (2 * (2) + 2 + 1)
            * (time s v K N (j + 1) - time s v K N j))
          * ((band d).scale (E N) N (time s v K N j)) ^ (2 * (2) + 2 - 1)
          ≤ 2 * (N : ℝ) ^ ε₁ * Λ) →
      (∀ j < K N, ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ 2 * (2) + 2 →
        (d.W N : ℝ) ^ (-D') + (ℓ : ℝ) * ((etaT (E N) (time s v K N (j + 1)))⁻¹ ^ (ℓ + 1)
            * (time s v K N (j + 1) - time s v K N j)) ≤ (d.W N : ℝ) ^ (-(D' - 1))) →
      ∃ G : Set (Ωg d), (Pg d).real Gᶜ ≤ (N : ℝ) ^ (-D₁)
        ∧ ∀ ω ∈ G, 0 < goodExitTau514 d (E N) s v K (2) ε₁ Λ Φ τ' D' ℓs N ω →
          ∀ a : LoopArg (d.L N) (2),
            ‖Afroz514 d (E N) s v K N σ (goodExitTau514 d (E N) s v K (2) ε₁ Λ Φ τ' D' ℓs N)
                (goodExitTau514 d (E N) s v K (2) ε₁ Λ Φ τ' D' ℓs N ω) ω a‖
              ≤ kappa514 (d.L N) (2) (E N) (4 * (d.W N : ℝ) ^ τ') (time s v K N) 0
                    (goodExitTau514 d (E N) s v K (2) ε₁ Λ Φ τ' D' ℓs N ω)
                  * (Finset.univ.sup' Finset.univ_nonempty
                      (fun b => ‖AtrueN d (E N) s v K N σ 0 ω b‖))
                + eps514 (2) (time s v K N) 0
                    (goodExitTau514 d (E N) s v K (2) ε₁ Λ Φ τ' D' ℓs N ω)
                  * (d.W N : ℝ) ^ (-D')
                + step s v K N * ∑ j ∈ Finset.range
                    (goodExitTau514 d (E N) s v K (2) ε₁ Λ Φ τ' D' ℓs N ω),
                    (kappa514 (d.L N) (2) (E N) (4 * (d.W N : ℝ) ^ τ') (time s v K N) (j + 1)
                        (goodExitTau514 d (E N) s v K (2) ε₁ Λ Φ τ' D' ℓs N ω)
                      * dDr514 d (E N) N (2) (time s v K N j) ε₁ τ' D' Φ CK
                          (MD514 d (E N) N (2) (CK + 1) (time s v K N j)
                            * (band d).scale (E N) N (time s v K N j) ^ (2))
                    + eps514 (2) (time s v K N) (j + 1)
                        (goodExitTau514 d (E N) s v K (2) ε₁ Λ Φ τ' D' ℓs N ω)
                      * driftErr514 d N 0 (CK + 1)
                          (MD514 d (E N) N (2) (CK + 1) (time s v K N j)) D')
                + (N : ℝ) ^ ε₁ * Real.sqrt (∑ j ∈ Finset.range
                    (goodExitTau514 d (E N) s v K (2) ε₁ Λ Φ τ' D' ℓs N ω),
                    (cQV514 d (E N) s v K N (2) τ' (D' - 1) (2 * (N : ℝ) ^ ε₁ * Λ)
                      (goodExitTau514 d (E N) s v K (2) ε₁ Λ Φ τ' D' ℓs N ω) a j : ℝ))
                + (N : ℝ) ^ (-D_Y)
                + ∑ j ∈ Finset.range (goodExitTau514 d (E N) s v K (2) ε₁ Λ Φ τ' D' ℓs N ω),
                    (1 + (1 - time s v K N
                      (goodExitTau514 d (E N) s v K (2) ε₁ Λ Φ τ' D' ℓs N ω))⁻¹) ^ (2)
                    * stepErrN (band d) (E N) N (2) (time s v K N j) (time s v K N (j + 1))
                        (step s v K N) (CK + 1) := by
  filter_upwards [grid_assembly_at_tau' (μ := Pg d) (ℱ := filt d) (2) hε₁ D_Y D₁ 1 C_P C_K
    hCK0 hCK] with N hN
  intro Λ Φ ℓs hΛ0 hΦ0 hs0 hsv hv1 hK1 hK hΔK hL hA1 hreg hPY hshΞ hshD
  -- abbreviations
  have hn2 : 2 ≤ 2 := by omega
  set u := time s v K N with hu
  set Δ := step s v K N with hΔ
  set τ := goodExitTau514 d (E N) s v K (2) ε₁ Λ Φ τ' D' ℓs N with hτ
  set ξ := xiOf (mSigma (E N)) σ with hξ
  set Kd : ℝ := 4 * (d.W N : ℝ) ^ τ' with hKd
  have hK0 : K N ≠ 0 := by omega
  have hΔ0 : 0 ≤ Δ := div_nonneg (by linarith) (Nat.cast_nonneg _)
  have hmem : ∀ i, i ≤ K N → u i ∈ Set.Icc (s N) (v N) :=
    fun i hi => mem_Icc_time s v K N i hs0 hsv.le hi
  have hu0 : ∀ i ≤ K N, 0 ≤ u i := fun i hi => hs0.trans (hmem i hi).1
  have hu1 : ∀ i ≤ K N, u i < 1 := fun i hi => (hmem i hi).2.trans_lt hv1
  have hmono : ∀ i k, i ≤ k → k ≤ K N → u i ≤ u k := by
    intro i k hik hk
    show s N + (i : ℝ) * Δ ≤ s N + (k : ℝ) * Δ
    have : (i : ℝ) ≤ (k : ℝ) := by exact_mod_cast hik
    nlinarith
  have hW1 : (1 : ℝ) ≤ (d.W N : ℝ) ^ τ' := Real.one_le_rpow (by exact_mod_cast d.W_pos N) hτ'.le
  have hKd1 : 1 ≤ Kd := by rw [hKd]; linarith
  have hKdW : (d.W N : ℝ) ^ τ' ≤ Kd := by rw [hKd]; linarith
  have hτK : ∀ ω, τ ω ≤ K N := fun ω => goodExitTau514_le d (E N) s v K (2) ε₁ Λ Φ τ' D' ℓs N ω
  have hτmeas : ∀ j, MeasurableSet[filt d j] {ω | j < τ ω} :=
    fun j => lt_goodExitTau514_measurableSet d s v K (2) ε₁ Λ Φ τ' D' ℓs N j
  have hmemτ : ∀ ω j, j < τ ω → H d s v K N j ω ∈ goodSet514 d (E N) N (u j) (2) ε₁ Λ Φ τ' D' ℓs :=
    fun ω j h => mem_goodSet514_of_lt_goodExitTau514 d h
  have hAgrid : ∀ j ≤ K N, 1 ≤ (band d).scale (E N) N (u j) :=
    fun j hj => hA1 (u j) (hu0 j hj) (hmem j hj).2
  -- the `K` envelope on `[0, u_{j+1}]`
  have hBk : ∀ j < K N, ∀ w ∈ Set.Icc (0 : ℝ) (u (j + 1)), ∀ J : LoopIdx (ZMod (d.L N)),
      J.WF → 2 ≤ J.length → J.length ≤ (2) → ‖(band d).Kval (E N) N w J‖ ≤ CK + 1 := by
    intro j hj w hw J hJ h2 hln
    have hwv : w ≤ v N := hw.2.trans (hmem (j + 1) (by omega)).2
    exact (hKenv N w hw.1 (hwv.trans_lt hv1) (hA1 w hw.1 hwv)).2 J hJ hln
  have hξb : ∀ j ≤ K N, ∀ a : LoopArg (d.L N) (2), ‖(u j : ℂ) * xiLoop (mSigma (E N))
      (⟨List.ofFn σ, List.ofFn a⟩ : LoopIdx (ZMod (d.L N))) ((2) - 1)‖ < 1 :=
    fun j hj a => norm_time_mul_xiLoop_lt (hE N) _ _ (hu0 j hj) (hu1 j hj)
  have hstepErr : ∀ j < K N, 0 ≤ stepErrN (band d) (E N) N (2) (u j) (u (j + 1)) Δ (CK + 1)
      ∧ ∀ᵐ ω ∂(Pg d), RgridT d (E N) s v K N σ (CK + 1) j ω = RgridN d (E N) s v K N σ j ω :=
    fun j hj => RgridT_ae d (E N) (hE N) s v K N j hsv hj (hu0 j hj.le) (hu1 (j + 1) (by omega)) hn2 σ
      (by linarith) (hBk j hj) (hξb j hj.le)
  -- the data
  set A0 : Ωg d → LoopArg (d.L N) (2) → ℂ := AtrueN d (E N) s v K N σ 0 with hA0
  set A : ℕ → Ωg d → LoopArg (d.L N) (2) → ℂ := Afroz514 d (E N) s v K N σ τ with hAdef
  set Dr : ℕ → Ωg d → LoopArg (d.L N) (2) → ℂ := DgridN d (E N) s v K N σ with hDr
  set Z : ℕ → Ωg d → LoopArg (d.L N) (2) → ℂ := gridZC d s v K N (2) (gridΦG d (E N) s v K N σ) with hZ
  set Y : ℕ → Ωg d → LoopArg (d.L N) (2) → ℂ := gridYC d s v K N (2) (gridΦG d (E N) s v K N σ) with hY
  set R : ℕ → Ωg d → LoopArg (d.L N) (2) → ℂ := RgridT d (E N) s v K N σ (CK + 1) with hR
  set κ : ℕ → ℕ → ℝ := kappa514 (d.L N) (2) (E N) Kd u with hκ
  set εK : ℕ → ℕ → ℝ := eps514 (2) u with hεK
  set δ0 : ℝ := (d.W N : ℝ) ^ (-D') with hδ0
  set dDrift : ℕ → Ωg d → ℝ := fun j _ => dDr514 d (E N) N (2) (u j) ε₁ τ' D' Φ CK
    (MD514 d (E N) N (2) (CK + 1) (u j) * (band d).scale (E N) N (u j) ^ (2)) with hdD
  set δD : ℕ → Ωg d → ℝ := fun j _ => driftErr514 d N 0 (CK + 1) (MD514 d (E N) N (2) (CK + 1) (u j)) D'
    with hδD
  set c := cQV514 d (E N) s v K N (2) τ' (D' - 1) (2 * (N : ℝ) ^ ε₁ * Λ) with hc
  set vv : ℕ → ℝ := fun _ => vY514 d N (2) (v N) (etaT (E N) (v N)) Δ with hvv
  set ww : ℕ → ℝ := fun _ => wY514 d N (2) (v N) (etaT (E N) (v N)) Δ with hww
  set stepErr : ℕ → ℝ := fun j => stepErrN (band d) (E N) N (2) (u j) (u (j + 1)) Δ (CK + 1) with hsE
  set PP := PY514 d N (2) (v N) (etaT (E N) (v N)) with hPP
  have hMK0 : 0 ≤ CK + 1 := by linarith
  have hMD0 : ∀ j ≤ K N, 0 ≤ MD514 d (E N) N (2) (CK + 1) (u j) := by
    intro j hj
    unfold MD514
    have := etaT_pos (hE N) (hu1 j hj)
    positivity
  have hPW : GridAssemblyHypPW (Pg d) (filt d) (d.L N) ξ u τ Δ (K N) Kd false A0 A Dr Z Y R
      κ εK δ0 dDrift δD c vv ww stepErr :=
    { hL3 := d.three_le_L N
      hξ := fun p => (norm_xiOf_mSigma (hE N).le σ p).le
      hu0 := hu0
      hu1 := hu1
      hΔ0 := hΔ0
      hexp := hexp514 d (E N) (hE N) σ s v K N hs0 hsv hv1 hK0 hn2 (Bk := CK + 1) (by linarith) hBk τ hτK
      hκ0 := fun i k hik hk => kappa514_nonneg (d.three_le_L N) (by linarith) u
        (hu0 i (hik.trans hk)) (hu1 i (hik.trans hk)) (hu0 k hk) (hu1 k hk)
      hε0 := fun i k hik hk => eps514_nonneg (2) u (hu1 i (hik.trans hk)) (hu1 k hk)
      hker := hker_of_Q716_nonAlt (d.L N) (d.three_le_L N) (hE N) hk0 hu0 hmono hu1 hKd1
      hδ0 := Real.rpow_nonneg (by positivity) _
      hA0cls := fun ω hτ0 => kerClass_A0 d s v K N σ ω (hmemτ ω 0 hτ0) hKdW
      hdDrift0 := fun ω j hj => dDr514_nonneg d (hE N) N (2) (hu1 j hj.le)
        (lt_of_lt_of_le one_pos (hAgrid j hj.le)) hΦ0 hCK0'
        (mul_nonneg (hMD0 j hj.le) (pow_nonneg (le_trans zero_le_one (hAgrid j hj.le)) _))
      hδD0 := fun ω j hj => driftErr514_nonneg d N 0 hMK0 (hMD0 j hj.le)
      hdrift := fun ω j hj hjτ b => norm_DgridN_le' d hn2 (hE N) s v K N σ j ω hτ' (by linarith) hΦ0
        (hu0 j hj.le) (hu1 j hj.le) (hAgrid j hj.le) hreg (hmemτ ω j hjτ) hCK0'
        (hKenv N (u j) (hu0 j hj.le) (hu1 j hj.le) (hAgrid j hj.le)).1
        (mul_nonneg (hMD0 j hj.le) (pow_nonneg (le_trans zero_le_one (hAgrid j hj.le)) _))
        (fun m' _ hm' => xiLKM_crude d (hE N) (H_isHermitian d s v K N j ω) (hu0 j hj.le)
          (hu1 j hj.le) (hAgrid j hj.le)
          (hKenv N (u j) (hu0 j hj.le) (hu1 j hj.le) (hAgrid j hj.le)).2 hm') b
      hDcls := fun ω j hj hjτ => kerClass_drift d (hE N) s v K N σ j ω hτ' (by linarith)
        (hu0 j hj.le) (hmono j (j + 1) (by omega) (by omega)) (hu1 (j + 1) (by omega)) hreg
        (hmemτ ω j hjτ) hMK0 (hMD0 j hj.le)
        (hKenv N (u j) (hu0 j hj.le) (hu1 j hj.le) (hAgrid j hj.le)).2
        (fun J hJ hln => norm_lk_env d (hE N) (H_isHermitian d s v K N j ω) (hu0 j hj.le)
          (hu1 j hj.le) (hKenv N (u j) (hu0 j hj.le) (hu1 j hj.le) (hAgrid j hj.le)).2 J hJ hln)
      hc_pos := cQV514_sum_pos d (hE N) s v K N hs0 hsv hv1 (by positivity)
      hYmeas := stronglyMeasurable_gridYC d s v K N (2) (gridΦG d (E N) s v K N σ)
        (gridΦG_testFun d (hE N) hsv.le hv1 hK0 (by omega) σ)
      hv0 := fun j _ => by
        show 0 ≤ vY514 d N (2) (v N) (etaT (E N) (v N)) Δ
        unfold vY514
        exact mul_nonneg (sq_nonneg _) (integral_nonneg fun _ => sq_nonneg _)
      hw0 := fun j _ => by
        show 0 ≤ wY514 d N (2) (v N) (etaT (E N) (v N)) Δ
        unfold wY514
        exact mul_nonneg (by positivity) (integral_nonneg fun _ => by positivity)
      hYmeanRe := fun k hk b j hj =>
        (Y_fields514 d (hE N) s v K N hs0 hsv.le hv1 hK0 σ τ hτmeas k hk b j hj).1
      hYmeanIm := fun k hk b j hj =>
        (Y_fields514 d (hE N) s v K N hs0 hsv.le hv1 hK0 σ τ hτmeas k hk b j hj).2.1
      hYintRe := fun k hk b j hj =>
        (Y_fields514 d (hE N) s v K N hs0 hsv.le hv1 hK0 σ τ hτmeas k hk b j hj).2.2.1
      hYintIm := fun k hk b j hj =>
        (Y_fields514 d (hE N) s v K N hs0 hsv.le hv1 hK0 σ τ hτmeas k hk b j hj).2.2.2.1
      hYcondRe := fun k hk b j hj =>
        (Y_fields514 d (hE N) s v K N hs0 hsv.le hv1 hK0 σ τ hτmeas k hk b j hj).2.2.2.2.1
      hYcondIm := fun k hk b j hj =>
        (Y_fields514 d (hE N) s v K N hs0 hsv.le hv1 hK0 σ τ hτmeas k hk b j hj).2.2.2.2.2.1
      hY4Re := fun k hk b j hj =>
        (Y_fields514 d (hE N) s v K N hs0 hsv.le hv1 hK0 σ τ hτmeas k hk b j hj).2.2.2.2.2.2.1
      hY4Im := fun k hk b j hj =>
        (Y_fields514 d (hE N) s v K N hs0 hsv.le hv1 hK0 σ τ hτmeas k hk b j hj).2.2.2.2.2.2.2
      hstepErr0 := fun j hj => (hstepErr j hj).1
      hR := fun ω j hj _ b => norm_RgridT_le d (E N) s v K N σ (CK + 1) j (hstepErr j hj).1 ω b }
  have hqv := hqv514 d (hE N) s v K N σ hk0 hs0 hsv.le hv1 hK0 τ hτmeas (Φq := 2 * (N : ℝ) ^ ε₁ * Λ)
    (D'' := D' - 1) hτ'.le hmemτ hAgrid hshΞ (fun j hj ℓ h1 h2 => by
      have := hshD j hj ℓ h1 h2
      simpa [neg_sub] using this)
  have hZmeas := stronglyMeasurable_gridZC s v K N (2) (gridΦG d (E N) s v K N σ)
    (gridΦG_testFun d (hE N) hsv.le hv1 hK0 (by omega) σ)
  have hKΔ : (K N : ℝ) * Δ ≤ 1 := by
    have hKpos : (0 : ℝ) < K N := by exact_mod_cast (by omega : 0 < K N)
    rw [hΔ]; unfold step
    rw [mul_div_cancel₀ _ hKpos.ne']
    linarith [hs0, hv1]
  have hP0 : 0 ≤ PP := by
    rw [hPP]; unfold PY514
    have h2 : 0 ≤ ∫ x, (‖Xmat d N x‖ ^ 2 + ∫ y, ‖Xmat d N y‖ ^ 2 ∂(P d)) ^ 2 ∂(P d) :=
      integral_nonneg fun x => by positivity
    have h4 : 0 ≤ ∫ x, (‖Xmat d N x‖ ^ 2 + ∫ y, ‖Xmat d N y‖ ^ 2 ∂(P d)) ^ 4 ∂(P d) :=
      integral_nonneg fun x => by positivity
    exact mul_nonneg (sq_nonneg _) (by linarith)
  have hvw := vY_wY_le d N (2) (v N) (etaT (E N) (v N)) Δ
  exact hN (K N) (d.L N) hK1 hK hL ξ u τ Δ Kd false A0 A Dr Z Y R κ εK δ0 dDrift δD c vv ww
    stepErr PP hΔK hKΔ hP0 hPY (fun j _ => hvw.1) (fun j _ => hvw.2) hτmeas hZmeas hqv hPW hτK

end Assembly514TwoN

section EndpointTwoN

/-! ### A private helper

`cKerShort` is antitone in its real argument (its only `κ`-dependence is the term
`cShort / κ * cWin ^ (n - 1)`, `cShort, cWin ≥ 0`), used below. It is the same statement as
`cKerShort_anti` of `EnergyN/Gauss/Lemma514NonAlt.lean`, proved again here because Lean
`private` is file-local. -/

private theorem cKerShort_anti (n : ℕ) {x1 x2 : ℝ} (hx1 : 0 < x1) (hx12 : x1 ≤ x2) :
    cKerShort n x2 ≤ cKerShort n x1 := by
  unfold cKerShort
  have h1 : cShort / x2 ≤ cShort / x1 := div_le_div_of_nonneg_left cShort_nonneg hx1 hx12
  have h2 : (0 : ℝ) ≤ cWin ^ (n - 1) := pow_nonneg cWin_nonneg _
  linarith [mul_le_mul_of_nonneg_right h1 h2]

set_option maxHeartbeats 16000000 in
theorem endpoint_nonAlt_two_ite_plainN {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) {E : ℕ → ℝ}
    (hEκ : ∀ N, |E N| ≤ 2 - κ) {s t : ℕ → ℝ} (hB : BoundsCoreN (sample d) E s) (hs0 : ∀ N, 0 ≤ s N)
    (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c)
    (hreg0 : ∀ᶠ N : ℕ in atTop, (etaT (E N) (s N) / etaT (E N) (t N)) ^ 30 ≤
      (band d).scale (E N) N (t N))
    (hAc : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale (E N) N (t N)) :
    ∀ Λ Φ : ℕ → ℝ, (∀ N, 0 ≤ Λ N) → (∀ N, 0 ≤ Φ N) →
      (∀ᶠ N : ℕ in atTop, 1 ≤ Λ N) → Lemma514PremisesN (sample d) E s t (2) Λ Φ →
      ∀ v : ℕ → ℝ, (∀ N, v N ∈ Set.Icc (s N) (t N)) →
        StochDom (band d).P
          (fun N (q : LoopData ((band d).L N) (2)) ω =>
            if SumZeroDyn.NonAlt q.1 then ‖SumZeroDyn.lkT (sample d) (E N) N (v N) ω q.1 q.2‖ else 0)
          (fun N _ _ => (Λ N ^ ((1 : ℝ) / 2) + Φ N) * ((band d).scale (E N) N (v N) ^ (2))⁻¹) := by
  intro Λ Φ hΛ0 hΦ0 hΛ1 hprem v hv
  have hE : ∀ N, |E N| < 2 := fun N => by linarith [hEκ N]
  have hsv : ∀ N, s N ≤ v N := fun N => (hv N).1
  have hvt : ∀ N, v N ≤ t N := fun N => (hv N).2
  have hv1 : ∀ N, v N < 1 := fun N => (hvt N).trans_lt (ht1 N)
  obtain ⟨hreg0_v, hAc_v⟩ := hreg_sub514_plainN d hE hsv hvt ht1 hreg0 hAc
  have hcond_v : Cond272N (band d) E s v := Step2.cond272_of_plainN hE hsv hv1 hreg0_v
  obtain ⟨CK, hCK0, hKenv0⟩ := exists_Kval_env_unif d hκ0 hκ1 (2) (by omega)
  have hKenv := fun (N : ℕ) (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u < 1)
      (hA1 : 1 ≤ (band d).scale (E N) N u) => hKenv0 (E N) (hEκ N) N u hu0 hu1 hA1
  obtain ⟨hP1, hP2, hP3, hP4⟩ := hprem
  intro ε hε D hD
  -- the exponents, functions of `(ε, D, n)` only
  set nR : ℝ := ((2 : ℕ) : ℝ) with hnR
  have hnRm : nR = (2 : ℝ) := by rw [hnR]; norm_num
  set ε₀ : ℝ := min ε 1 with hε₀
  have hε₀0 : 0 < ε₀ := lt_min hε one_pos
  have hε₀1 : ε₀ ≤ 1 := min_le_right _ _
  have hε₀ε : ε₀ ≤ ε := min_le_left _ _
  set ε₁ : ℝ := ε₀ / 8 with hε₁
  set τ' : ℝ := ε₀ / (8 * (2 * nR + 2)) with hτ'
  set D' : ℝ := 12 * nR + 24 with hD'
  set D_Y : ℝ := nR + 1 with hD_Y
  set C_P : ℝ := 8 * nR + 7 with hC_P
  set C_K : ℝ := (D + 1) + 4 * D_Y + nR * 1 + 2 * C_P + 8 + D' + 8 * nR + 40 with hC_K
  set K : ℕ → ℕ := Kc C_K with hK
  have hε₁0 : 0 < ε₁ := by rw [hε₁]; linarith
  have hden : 0 < 8 * (2 * nR + 2) := by linarith
  have hτ'0 : 0 < τ' := by rw [hτ']; exact div_pos hε₀0 hden
  have hτeq : τ' * (8 * (2 * nR + 2)) = ε₀ := by rw [hτ']; field_simp
  have hC_K0 : 0 ≤ C_K := by rw [hC_K]; linarith
  have hK0 : ∀ N, K N ≠ 0 := Kc_ne_zero C_K
  have hKcard := ev_Kcard C_K hC_K0
  have hC1 : (0 : ℝ) ≤ C_K + 1 := by linarith
  -- the four grid premises (flow → grid)
  have hYΛ : StochDom (Pg d) (fun N (k : Fin (K N + 1)) ω =>
      xiLM d (E N) N (time s v K N k) (H d s v K N k ω) (2 * (2) + 2)) (fun N _ _ => Λ N) :=
    stochDom_grid_of_flow514 d K hs0 hsv hvt hK0 hC1 hKcard
      (fun N u M => xiLM d (E N) N u M (2 * (2) + 2)) (fun N u => measurable_xiLM d (E N) N u _) Λ hP1
  have hXΦlt : ∀ m', 1 ≤ m' → m' < 2 → StochDom (Pg d) (fun N (k : Fin (K N + 1)) ω =>
      xiLKM d (E N) N (time s v K N k) (H d s v K N k ω) m') (fun N _ _ => Φ N) := fun m' h1 h2 =>
    stochDom_grid_of_flow514 d K hs0 hsv hvt hK0 hC1 hKcard
      (fun N u M => xiLKM d (E N) N u M m') (fun N u => measurable_xiLKM d (E N) N u _) Φ (hP2 m' h1 h2)
  have hXΦprod : ∀ m', 2 ≤ m' → m' ≤ 2 → StochDom (Pg d) (fun N (k : Fin (K N + 1)) ω =>
      xiLKM d (E N) N (time s v K N k) (H d s v K N k ω) m'
        * xiLKM d (E N) N (time s v K N k) (H d s v K N k ω) (2 - m' + 2)
        / (band d).scale (E N) N (time s v K N k)) (fun N _ _ => Φ N) := fun m' h1 h2 => by
    have h := stochDom_grid_of_flow514 d K hs0 hsv hvt hK0 hC1 hKcard
      (fun N u M => xiLKM d (E N) N u M m' * xiLKM d (E N) N u M (2 - m' + 2) * ((band d).scale (E N) N u)⁻¹)
      (fun N u => ((measurable_xiLKM d (E N) N u _).mul (measurable_xiLKM d (E N) N u _)).mul_const _) Φ
      (hP3 m' h1 h2)
    simpa only [div_eq_mul_inv] using h
  have hYΦ : StochDom (Pg d) (fun N (k : Fin (K N + 1)) ω =>
      xiLM d (E N) N (time s v K N k) (H d s v K N k ω) (2 + 1)) (fun N _ _ => Φ N) :=
    stochDom_grid_of_flow514 d K hs0 hsv hvt hK0 hC1 hKcard
      (fun N u M => xiLM d (E N) N u M (2 + 1)) (fun N u => measurable_xiLM d (E N) N u _) Φ hP4
  have hGood := highProb_grid_goodSet514_plainN d hκ0 hκ1 hEκ hB hs0 hsv hv1 hcond_v hc0 hreg0_v
    hAc_v K hK0 hC1 hKcard (2) hτ'0 (D := D') (by rw [hD']; linarith) hε₁0 Λ Φ hYΛ hXΦlt hXΦprod
    hYΦ
  -- the assembly, for each of the finitely many non-alternating charges
  have hCKc : (D + 1) + 4 * D_Y + ((2 : ℕ) : ℝ) * 1 + 2 * C_P + 8 ≤ C_K := by
    rw [hC_K]; linarith
  have hasm := fun σ : {σ : Fin (2) → Bool // SumZeroDyn.NonAlt σ} =>
    assembly514_twoN d hE s v σ.1 (k0 := Classical.choose σ.2) (Classical.choose_spec σ.2)
      (D' := D') (D_Y := D_Y) (D₁ := D + 1) (C_P := C_P) (C_K := C_K) hε₁0 hτ'0
      (by rw [hD']; linarith) hC_K0 hCKc hCK0 hKenv K
  have hasmAll := Filter.eventually_all.2 hasm
  -- the remaining eventual facts
  set κ' : ℝ := min κ 1 with hκ'def
  have hκ'0 : 0 < κ' := lt_min hκ0 one_pos
  have hκ'1 : κ' ≤ 1 := min_le_right _ _
  have hκ'2 : κ' ≤ 2 := hκ'1.trans (by norm_num)
  have hEκ' : ∀ N, |E N| ≤ 2 - κ' := fun N => (hEκ N).trans (by linarith [min_le_left κ 1])
  set mκ : ℝ := Real.sqrt (2 * κ') / 2 with hmκdef
  have hmκpos : 0 < mκ := by positivity
  have hmge : ∀ N, mκ ≤ (mE (E N)).im := fun N => mE_im_ge hκ'0 hκ'2 (hEκ' N)
  have hminκ'_le : ∀ N, κ' ≤ min (2 - |E N|) 1 := fun N => min_le_min (by linarith [hEκ N]) le_rfl
  set cK := cKerShort (2) (Real.sqrt κ') with hcK
  set cK2 := cKerShort ((2) + (2)) (Real.sqrt κ') with hcK2
  have hcK0 : 0 ≤ cK := cKerShort_nonneg _ (Real.sqrt_nonneg _)
  have hcK20 : 0 ≤ cK2 := cKerShort_nonneg _ (Real.sqrt_nonneg _)
  have hcK_le : ∀ N, cKerShort (2) (Real.sqrt (min (2 - |E N|) 1)) ≤ cK := fun N => by
    rw [hcK]
    exact cKerShort_anti (2) (Real.sqrt_pos.2 hκ'0) (Real.sqrt_le_sqrt (hminκ'_le N))
  have hcK2_le : ∀ N, cKerShort ((2) + (2)) (Real.sqrt (min (2 - |E N|) 1)) ≤ cK2 := fun N => by
    rw [hcK2]
    exact cKerShort_anti ((2) + (2)) (Real.sqrt_pos.2 hκ'0) (Real.sqrt_le_sqrt (hminκ'_le N))
  have hnτ : nR * τ' ≤ ε₀ / 16 := by nlinarith
  have hInit := ev_init514N d hB (n := 2) (by omega) hs0 hsv K hK0 hε₁0 (D := D + 1) (by linarith)
  have hlog := sum_step_div_eta_le_plainN d hE hs0 hsv hv1 hc0 hreg0_v hAc_v K hK0
  have hη := etaT_inv_le_of_plainN (band d) hE hv1 hc0 hAc_v
  have hA := scale_ge_one_of_hreg_plainN d hE hsv hv1 hc0 hreg0_v hAc_v
  have hKD := eventually_kDecayRegime d (2) hτ'0 D'
  have hPY := ev_rpow_le (a := ((8 * (2) + 6 : ℕ) : ℝ)) (b := C_P)
    (by rw [hC_P, hnR]; push_cast; linarith) (857 * 1024 ^ (2) * nR ^ 4)
  have ha1 := ev_ha1 d (2) (ε₀ := ε₀) (ε₁ := ε₁) hτ'0.le (by rw [hε₁]; linarith) hcK0
  have ha2 := ev_ha2 d (2) (ε₀ := ε₀) (ε₁ := ε₁) (CK := CK) hτ'0.le hε₁0.le
    (by rw [hε₁]; nlinarith) hcK0 hCK0 hmκpos
  have ha3 := ev_ha3 d (2) (ε₀ := ε₀) (ε₁ := ε₁) (cK2 := cK2) hτ'0.le
    (by rw [hε₁]; nlinarith) hcK20 hmκpos
  have he1 := ev_he1 d (2) hε₀0.le (D' := D') (by rw [hD']; linarith)
  have he2 := ev_he2 d 0 (ε₁ := ε₁) (D' := D') (cK := cK) hε₀0.le (by rw [hε₁]; linarith)
    hτ'0.le (by linarith) (by rw [hD']; linarith) hcK0 hCK0
  have he3 := ev_he3 d (2) (ε₁ := ε₁) (τ' := τ') (D' := D') (cK2 := cK2) hε₀0.le
    (by rw [hε₁]; linarith) hτ'0.le (by push_cast; nlinarith [hnRm]) (by rw [hD']; linarith) hcK20
  have he4 := ev_he4 (2) hε₀0.le
  have he5 := ev_he5 (2) hε₀0.le (C_K := C_K) (by rw [hC_K, hD', hD_Y, hC_P]; linarith)
  have hshX := ev_rpow_le (a := ((2 * (2 * (2) + 2) : ℕ) : ℝ) - C_K) (b := 0)
    (by rw [hC_K, hD', hD_Y, hC_P]; push_cast; linarith [hnRm]) ((2 * (2) + 2 : ℕ) : ℝ)
  have hshD := ev_rpow_le (a := ((2 * (2) + 2 + 1 : ℕ) : ℝ) - C_K) (b := -D')
    (by rw [hC_K, hD', hD_Y, hC_P]; push_cast; linarith [hnRm]) ((2 * (2) + 2 : ℕ) : ℝ)
  have hΔN := ev_rpow_le (a := 1 - C_K) (b := 0) (by rw [hC_K, hD', hD_Y, hC_P]; linarith) 2
  have hLmK := hB.LmK (2) (by omega) ε hε D hD
  have hGoodD := hGood (D + 1) (by linarith)
  filter_upwards [hLmK, hΛ1, hasmAll, hGoodD, hInit, eventually_ge_atTop (2 ^ (2) + 2), hlog,
    hη, ev_dims514 d, hA, hKD, hPY, ha1, ha2, ha3, he1, he2, he3, he4, he5, hshX, hshD, hΔN,
    eventually_ge_atTop ⌈CK + 1⌉₊] with N hLmKN hΛN hasmN hGoodN hInitN hN2N hlogN hηN hdN hAN
    hKDN hPYN ha1N ha2N ha3N he1N he2N he3N he4N he5N hshXN hshDN hΔNN hCKNN
  obtain ⟨hN1, hW2, hWN, hLN, hLWN, hcardN, hsqN⟩ := hdN
  have hN1n : 1 ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  have hNε : (N : ℝ) ^ ε₀ ≤ (N : ℝ) ^ ε := Real.rpow_le_rpow_of_exponent_le hN1 hε₀ε
  have hAv0 : 0 < (band d).scale (E N) N (v N) := (band d).scale_pos' (hE N) N ((hs0 N).trans (hsv N)) (hv1 N)
  set g : ℝ := (Λ N ^ ((1 : ℝ) / 2) + Φ N) * ((band d).scale (E N) N (v N) ^ (2))⁻¹ with hg
  have hΛh : 1 ≤ Λ N ^ ((1 : ℝ) / 2) := Real.one_le_rpow hΛN (by norm_num)
  have hg0 : 0 ≤ g := by rw [hg]; have := hΦ0 N; positivity
  have hNεg : 0 ≤ (N : ℝ) ^ ε * g := mul_nonneg (Real.rpow_nonneg hN0.le _) hg0
  by_cases hsvN : s N = v N
  · -- the degenerate window `s N = v N`: directly (2.68) at `s`
    refine le_trans (measure_mono ?_) hLmKN
    intro ω hω
    obtain ⟨q, hq⟩ := hω
    refine ⟨q, ?_⟩
    change (N : ℝ) ^ ε * g < (if SumZeroDyn.NonAlt q.1 then
      ‖SumZeroDyn.lkT (sample d) (E N) N (v N) ω q.1 q.2‖ else 0) at hq
    change (N : ℝ) ^ ε * ((band d).scale (E N) N (s N))⁻¹ ^ (2) < (sample d).lkErr (E N) N (s N) ω q.idx
    split_ifs at hq with hna
    · have e1 : ‖SumZeroDyn.lkT (sample d) (E N) N (v N) ω q.1 q.2‖ = (sample d).lkErr (E N) N (s N) ω q.idx := by
        rw [SumZeroDyn.norm_lkT, ← hsvN]
      rw [e1] at hq
      have hle : ((band d).scale (E N) N (s N))⁻¹ ^ (2) ≤ g := by
        rw [hg, hsvN, inv_pow]
        have h0 : 0 ≤ ((band d).scale (E N) N (v N) ^ (2))⁻¹ := by positivity
        have : 1 ≤ Λ N ^ ((1 : ℝ) / 2) + Φ N := by linarith [hΦ0 N]
        nlinarith
      have := mul_le_mul_of_nonneg_left hle (Real.rpow_nonneg hN0.le ε)
      linarith
    · linarith
  · have hlt : s N < v N := lt_of_le_of_ne (hsv N) hsvN
    have hKN1 : 1 ≤ K N := Nat.one_le_iff_ne_zero.mpr (hK0 N)
    have hKle : K N ≤ ⌈(N : ℝ) ^ C_K⌉₊ := Kc_le_ceil C_K hN1n
    have hΔ : step s v K N ≤ (N : ℝ) ^ (-C_K) := step_Kc_le C_K hN1n (hs0 N) (hv1 N)
    have hΔ0 : 0 ≤ step s v K N := div_nonneg (by linarith [hsv N]) (Nat.cast_nonneg _)
    have hmem : ∀ i ≤ K N, time s v K N i ∈ Set.Icc (s N) (v N) :=
      fun i hi => mem_Icc_time s v K N i (hs0 N) (hsv N) hi
    have hdiff : ∀ j, time s v K N (j + 1) - time s v K N j = step s v K N := by
      intro j; unfold time; push_cast; ring
    rw [Real.rpow_zero] at hshXN hΔNN
    have hshΞ : ∀ j < K N, (N : ℝ) ^ ε₁ * Λ N
        + ((2 * (2) + 2 : ℕ) : ℝ) * ((etaT (E N) (time s v K N (j + 1)))⁻¹ ^ (2 * (2) + 2 + 1)
            * (time s v K N (j + 1) - time s v K N j))
          * ((band d).scale (E N) N (time s v K N j)) ^ (2 * (2) + 2 - 1)
        ≤ 2 * (N : ℝ) ^ ε₁ * Λ N := by
      intro j hj
      have hj1 := hmem (j + 1) (by omega)
      have hj0 := hmem j hj.le
      have hx := (inv_eta_le_of (hE N) (hv1 N) hηN hj1.2).1
      have hx0 : 0 ≤ (etaT (E N) (time s v K N (j + 1)))⁻¹ :=
        inv_nonneg.mpr (etaT_pos (hE N) (hj1.2.trans_lt (hv1 N))).le
      have hA' := (scale_le_LW d (hE N) N ((hs0 N).trans hj0.1) (hj0.2.trans_lt (hv1 N))).trans hLWN
      have hA0 := ((band d).scale_pos' (hE N) N ((hs0 N).trans hj0.1) (hj0.2.trans_lt (hv1 N))).le
      have he' : 1 ≤ (N : ℝ) ^ ε₁ * Λ N :=
        one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hN1 hε₁0.le) hΛN
      rw [hdiff j]
      have := shXi_le (N := N) (C_K := C_K) (2 * (2) + 2) hN1 hx0 hx hA0 hA' hΔ0 hΔ hshXN he'
        (by omega)
      linarith
    have hshD' : ∀ j < K N, ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ 2 * (2) + 2 →
        (d.W N : ℝ) ^ (-D') + (ℓ : ℝ) * ((etaT (E N) (time s v K N (j + 1)))⁻¹ ^ (ℓ + 1)
            * (time s v K N (j + 1) - time s v K N j)) ≤ (d.W N : ℝ) ^ (-(D' - 1)) := by
      intro j hj ℓ _ hℓ
      have hj1 := hmem (j + 1) (by omega)
      have hx := (inv_eta_le_of (hE N) (hv1 N) hηN hj1.2).1
      have hηpos := etaT_pos (hE N) (hj1.2.trans_lt (hv1 N))
      have hx1 : 1 ≤ (etaT (E N) (time s v K N (j + 1)))⁻¹ :=
        (one_le_inv₀ hηpos).mpr (etaT_le_one (hE N) ((hs0 N).trans hj1.1))
      rw [hdiff j]
      exact shD_le hN1 hW2 hWN (by rw [hD']; linarith) hx1 hx hΔ0 hΔ hℓ hshDN
    have hPY' : PY514 d N (2) (v N) (etaT (E N) (v N)) ≤ (N : ℝ) ^ C_P := by
      refine (PY514_le d N (2) hN1 hcardN (hv1 N) (inv_eta_le_of (hE N) (hv1 N) hηN le_rfl).2
        (etaT_pos (hE N) (hv1 N)) hηN).trans ?_
      rw [natpow_eq_rpow (N : ℝ) (8 * (2) + 6)]; exact hPYN
    have hGex := fun σ : {σ : Fin (2) → Bool // SumZeroDyn.NonAlt σ} =>
      hasmN σ (Λ N) (Φ N) ((band d).ell N (s N)) (hΛ0 N) (hΦ0 N) (hs0 N) hlt (hv1 N) hKN1 hKle hΔ
        (by rw [Real.rpow_one]; exact hLN) hAN hKDN hPY' hshΞ hshD'
    choose G hGP hGb using hGex
    -- the flow bad set is a preimage under `H_v`
    set Sbad : Set (Matrix (d.Idx N) (d.Idx N) ℂ) := {M | ∃ q : LoopData (d.L N) (2),
      (N : ℝ) ^ ε * g < (if SumZeroDyn.NonAlt q.1 then
        ‖gloop (d.L N) (d.W N) M (zt (E N) (v N)) q.idx - (band d).Kval (E N) N (v N) q.idx‖ else 0)}
      with hSbad
    have hSm : MeasurableSet Sbad := by
      have : Sbad = ⋃ q : LoopData (d.L N) (2), {M | (N : ℝ) ^ ε * g <
          (if SumZeroDyn.NonAlt q.1 then
            ‖gloop (d.L N) (d.W N) M (zt (E N) (v N)) q.idx - (band d).Kval (E N) N (v N) q.idx‖ else 0)} := by
        ext M; simp [hSbad]
      rw [this]
      refine MeasurableSet.iUnion fun q => measurableSet_lt measurable_const ?_
      split_ifs
      · exact ((measurable_gloop_matrix d N _ _).sub measurable_const).norm
      · exact measurable_const
    set Good := {ω : Ωg d | ∀ k : Fin (K N + 1), H d s v K N k ω ∈ goodSet514 d (E N) N
      (time s v K N k) (2) ε₁ (Λ N) (Φ N) τ' D' ((band d).ell N (s N))} with hGooddef
    set Init := {ω : Ωg d | ∀ q : LoopData (d.L N) (2),
      ‖gloop (d.L N) (d.W N) (H d s v K N 0 ω) (zt (E N) (s N)) q.idx - (band d).Kval (E N) N (s N) q.idx‖
        ≤ (N : ℝ) ^ ε₁ * ((band d).scale (E N) N (s N))⁻¹ ^ (2)} with hInitdef
    have hsub : H d s v K N (K N) ⁻¹' Sbad ⊆ Goodᶜ ∪ Initᶜ ∪ ⋃ σ, (G σ)ᶜ := by
      intro ω hω
      by_contra hno
      simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_iUnion, not_or, not_exists,
        not_not] at hno
      obtain ⟨⟨hgood, hinit⟩, hG⟩ := hno
      obtain ⟨q, hq⟩ := hω
      have hna : SumZeroDyn.NonAlt q.1 := by
        by_contra h
        simp only [h, ↓reduceIte] at hq
        linarith
      simp only [hna, ↓reduceIte] at hq
      have hτK : goodExitTau514 d (E N) s v K (2) ε₁ (Λ N) (Φ N) τ' D' ((band d).ell N (s N)) N ω
          = K N := goodExitTau514_eq_of_forall_mem d (E N) s v K (2) ε₁ (Λ N) (Φ N) τ' D' _ N hgood
      have hb := hGb ⟨q.1, hna⟩ ω (hG ⟨q.1, hna⟩) (by rw [hτK]; omega) q.2
      dsimp only at hb
      rw [hτK] at hb
      rw [Afroz514_eq_of_eq d (hE N) (hs0 N) (hsv N) (hv1 N) q.1 hτK] at hb
      have hX0 : Finset.univ.sup' Finset.univ_nonempty
          (fun b => ‖AtrueN d (E N) s v K N q.1 0 ω b‖)
          ≤ (N : ℝ) ^ ε₁ * ((band d).scale (E N) N (s N))⁻¹ ^ (2) := by
        refine Finset.sup'_le _ _ fun b _ => ?_
        have e : AtrueN d (E N) s v K N q.1 0 ω b = gloop (d.L N) (d.W N) (H d s v K N 0 ω) (zt (E N) (s N))
            (LoopData.idx (q.1, b)) - (band d).Kval (E N) N (s N) (LoopData.idx (q.1, b)) := by
          unfold AtrueN LvalN KvN; rw [time_zero]; rfl
        rw [e]; exact hinit (q.1, b)
      have hCKN2 : CK + 1 ≤ 2 * (N : ℝ) := by
        have := (Nat.le_ceil (CK + 1)).trans (by exact_mod_cast hCKNN : (⌈CK + 1⌉₊ : ℝ) ≤ N)
        linarith
      have hΔN' : step s v K N * (2 * (N : ℝ)) ≤ 1 := by
        have e : (N : ℝ) ^ (-C_K) * (2 * (N : ℝ)) = 2 * (N : ℝ) ^ (1 - C_K) := by
          rw [show 1 - C_K = -C_K + 1 by ring, Real.rpow_add hN0, Real.rpow_one]; ring
        have := mul_le_mul_of_nonneg_right hΔ (by positivity : (0 : ℝ) ≤ 2 * (N : ℝ))
        linarith
      -- literal bounds at `E N` from the fixed `cK`/`cK2`/`mκ` facts
      have hlogN0 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN1n)
      have hmEpos : 0 < (mE (E N)).im := lt_of_lt_of_le hmκpos (hmge N)
      have hmiL0 : 0 ≤ (mE (E N)).im⁻¹ * Real.log N := mul_nonneg (inv_nonneg.mpr hmEpos.le) hlogN0
      have hMc0 : 0 ≤ Mc514 d N (2) ε₁ τ' CK := by
        unfold Mc514
        have h1 : (0 : ℝ) ≤ (d.W N : ℝ) ^ τ' := Real.rpow_nonneg (by positivity) _
        have h2 : (0 : ℝ) ≤ (N : ℝ) ^ ε₁ := Real.rpow_nonneg (by positivity) _
        positivity
      have hmiN_le : (mE (E N)).im⁻¹ ≤ mκ⁻¹ := inv_anti₀ hmκpos (hmge N)
      have ha1N' : cKerShort (2) (Real.sqrt (min (2 - |E N|) 1))
          * (4 * (d.W N : ℝ) ^ τ') ^ (2) * (N : ℝ) ^ ε₁ ≤ (N : ℝ) ^ ε₀ / 8 :=
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hcK_le N) (by positivity)) (by positivity)).trans ha1N
      have ha2N' : cKerShort (2) (Real.sqrt (min (2 - |E N|) 1))
          * (4 * (d.W N : ℝ) ^ τ') ^ (2) * Mc514 d N (2) ε₁ τ' CK
          * ((mE (E N)).im⁻¹ * Real.log N) ≤ (N : ℝ) ^ ε₀ / 8 := by
        have hstep1 : cKerShort (2) (Real.sqrt (min (2 - |E N|) 1))
            * (4 * (d.W N : ℝ) ^ τ') ^ (2) * Mc514 d N (2) ε₁ τ' CK
            ≤ cK * (4 * (d.W N : ℝ) ^ τ') ^ (2) * Mc514 d N (2) ε₁ τ' CK :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hcK_le N) (by positivity)) hMc0
        have hcoef0 : 0 ≤ cK * (4 * (d.W N : ℝ) ^ τ') ^ (2) * Mc514 d N (2) ε₁ τ' CK :=
          mul_nonneg (mul_nonneg hcK0 (by positivity)) hMc0
        have hstep2 : cK * (4 * (d.W N : ℝ) ^ τ') ^ (2) * Mc514 d N (2) ε₁ τ' CK
            * ((mE (E N)).im⁻¹ * Real.log N)
            ≤ cK * (4 * (d.W N : ℝ) ^ τ') ^ (2) * Mc514 d N (2) ε₁ τ' CK
            * (mκ⁻¹ * Real.log N) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hmiN_le hlogN0) hcoef0
        calc cKerShort (2) (Real.sqrt (min (2 - |E N|) 1))
              * (4 * (d.W N : ℝ) ^ τ') ^ (2) * Mc514 d N (2) ε₁ τ' CK
              * ((mE (E N)).im⁻¹ * Real.log N)
            ≤ cK * (4 * (d.W N : ℝ) ^ τ') ^ (2) * Mc514 d N (2) ε₁ τ' CK
              * ((mE (E N)).im⁻¹ * Real.log N) :=
              mul_le_mul_of_nonneg_right hstep1 hmiL0
          _ ≤ cK * (4 * (d.W N : ℝ) ^ τ') ^ (2) * Mc514 d N (2) ε₁ τ' CK
              * (mκ⁻¹ * Real.log N) := hstep2
          _ ≤ (N : ℝ) ^ ε₀ / 8 := ha2N
      have ha3N' : (N : ℝ) ^ ε₁ * Real.sqrt (cKerShort ((2) + (2))
            (Real.sqrt (min (2 - |E N|) 1)) * ((d.W N : ℝ) ^ τ') ^ ((2) + (2))
            * (6 * Real.exp 1 * ((2 : ℕ) : ℝ) ^ 2 * (d.W N : ℝ) ^ τ' * (2 * (N : ℝ) ^ ε₁))
            * ((mE (E N)).im⁻¹ * Real.log N + 1)) ≤ (N : ℝ) ^ ε₀ / 8 := by
        have hrest0 : (0 : ℝ) ≤ ((d.W N : ℝ) ^ τ') ^ ((2) + (2))
            * (6 * Real.exp 1 * ((2 : ℕ) : ℝ) ^ 2 * (d.W N : ℝ) ^ τ' * (2 * (N : ℝ) ^ ε₁)) := by
          positivity
        have hstep1 : cKerShort ((2) + (2)) (Real.sqrt (min (2 - |E N|) 1))
              * (((d.W N : ℝ) ^ τ') ^ ((2) + (2))
                * (6 * Real.exp 1 * ((2 : ℕ) : ℝ) ^ 2 * (d.W N : ℝ) ^ τ' * (2 * (N : ℝ) ^ ε₁)))
            ≤ cK2 * (((d.W N : ℝ) ^ τ') ^ ((2) + (2))
                * (6 * Real.exp 1 * ((2 : ℕ) : ℝ) ^ 2 * (d.W N : ℝ) ^ τ' * (2 * (N : ℝ) ^ ε₁))) :=
          mul_le_mul_of_nonneg_right (hcK2_le N) hrest0
        have hmi1_le : (mE (E N)).im⁻¹ * Real.log N + 1 ≤ mκ⁻¹ * Real.log N + 1 := by
          linarith [mul_le_mul_of_nonneg_right hmiN_le hlogN0]
        have hcoef0 : (0 : ℝ) ≤ cK2 * (((d.W N : ℝ) ^ τ') ^ ((2) + (2))
            * (6 * Real.exp 1 * ((2 : ℕ) : ℝ) ^ 2 * (d.W N : ℝ) ^ τ' * (2 * (N : ℝ) ^ ε₁))) :=
          mul_nonneg hcK20 hrest0
        have harg_le : cKerShort ((2) + (2)) (Real.sqrt (min (2 - |E N|) 1))
              * ((d.W N : ℝ) ^ τ') ^ ((2) + (2))
              * (6 * Real.exp 1 * ((2 : ℕ) : ℝ) ^ 2 * (d.W N : ℝ) ^ τ' * (2 * (N : ℝ) ^ ε₁))
              * ((mE (E N)).im⁻¹ * Real.log N + 1)
            ≤ cK2 * ((d.W N : ℝ) ^ τ') ^ ((2) + (2))
              * (6 * Real.exp 1 * ((2 : ℕ) : ℝ) ^ 2 * (d.W N : ℝ) ^ τ' * (2 * (N : ℝ) ^ ε₁))
              * (mκ⁻¹ * Real.log N + 1) := by
          have e1 : cKerShort ((2) + (2)) (Real.sqrt (min (2 - |E N|) 1))
              * ((d.W N : ℝ) ^ τ') ^ ((2) + (2))
              * (6 * Real.exp 1 * ((2 : ℕ) : ℝ) ^ 2 * (d.W N : ℝ) ^ τ' * (2 * (N : ℝ) ^ ε₁))
              = cKerShort ((2) + (2)) (Real.sqrt (min (2 - |E N|) 1))
                * (((d.W N : ℝ) ^ τ') ^ ((2) + (2))
                  * (6 * Real.exp 1 * ((2 : ℕ) : ℝ) ^ 2 * (d.W N : ℝ) ^ τ' * (2 * (N : ℝ) ^ ε₁))) := by
            ring
          have e2 : cK2 * ((d.W N : ℝ) ^ τ') ^ ((2) + (2))
              * (6 * Real.exp 1 * ((2 : ℕ) : ℝ) ^ 2 * (d.W N : ℝ) ^ τ' * (2 * (N : ℝ) ^ ε₁))
              = cK2 * (((d.W N : ℝ) ^ τ') ^ ((2) + (2))
                * (6 * Real.exp 1 * ((2 : ℕ) : ℝ) ^ 2 * (d.W N : ℝ) ^ τ' * (2 * (N : ℝ) ^ ε₁))) := by
            ring
          rw [e1, e2]
          calc cKerShort ((2) + (2)) (Real.sqrt (min (2 - |E N|) 1))
                * (((d.W N : ℝ) ^ τ') ^ ((2) + (2))
                  * (6 * Real.exp 1 * ((2 : ℕ) : ℝ) ^ 2 * (d.W N : ℝ) ^ τ' * (2 * (N : ℝ) ^ ε₁)))
                * ((mE (E N)).im⁻¹ * Real.log N + 1)
              ≤ cK2 * (((d.W N : ℝ) ^ τ') ^ ((2) + (2))
                  * (6 * Real.exp 1 * ((2 : ℕ) : ℝ) ^ 2 * (d.W N : ℝ) ^ τ' * (2 * (N : ℝ) ^ ε₁)))
                * ((mE (E N)).im⁻¹ * Real.log N + 1) :=
                mul_le_mul_of_nonneg_right hstep1 (by linarith [hmiL0])
            _ ≤ cK2 * (((d.W N : ℝ) ^ τ') ^ ((2) + (2))
                  * (6 * Real.exp 1 * ((2 : ℕ) : ℝ) ^ 2 * (d.W N : ℝ) ^ τ' * (2 * (N : ℝ) ^ ε₁)))
                * (mκ⁻¹ * Real.log N + 1) :=
                mul_le_mul_of_nonneg_left hmi1_le hcoef0
        exact (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt harg_le) (by positivity)).trans ha3N
      have he2N' : ∀ Φ' : ℝ, 0 ≤ Φ' →
          cKerShort (2) (Real.sqrt (min (2 - |E N|) 1)) * (4 * (d.W N : ℝ) ^ τ') ^ (2)
              * (N : ℝ) ^ (2)
              * Ec514 d N (2) ε₁ D' Φ' (((N : ℝ) + (N : ℝ) ^ (2) + CK + 1) * (N : ℝ) ^ (2))
            + (N : ℝ) ^ (2) * driftErr514 d N 0 (CK + 1)
                ((N : ℝ) + (N : ℝ) ^ (2) + CK + 1) D'
          ≤ (N : ℝ) ^ ε₀ / 16 * (1 + Φ') * (N : ℝ)⁻¹ ^ (2) := by
        intro Φ' hΦ'0
        have hEc0 : 0 ≤ Ec514 d N (2) ε₁ D' Φ'
            (((N : ℝ) + (N : ℝ) ^ (2) + CK + 1) * (N : ℝ) ^ (2)) := by
          unfold Ec514; positivity
        have hstep1 : cKerShort (2) (Real.sqrt (min (2 - |E N|) 1))
              * (4 * (d.W N : ℝ) ^ τ') ^ (2) * (N : ℝ) ^ (2)
              * Ec514 d N (2) ε₁ D' Φ' (((N : ℝ) + (N : ℝ) ^ (2) + CK + 1) * (N : ℝ) ^ (2))
            ≤ cK * (4 * (d.W N : ℝ) ^ τ') ^ (2) * (N : ℝ) ^ (2)
              * Ec514 d N (2) ε₁ D' Φ' (((N : ℝ) + (N : ℝ) ^ (2) + CK + 1) * (N : ℝ) ^ (2)) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hcK_le N) (by positivity))
              (by positivity)) hEc0
        exact (add_le_add hstep1 le_rfl).trans (he2N Φ' hΦ'0)
      have he3N' : (N : ℝ) ^ ε₁ * Real.sqrt ((cKerShort ((2) + (2))
            (Real.sqrt (min (2 - |E N|) 1)) * ((d.W N : ℝ) ^ τ') ^ ((2) + (2))
            * (N : ℝ) ^ ((2) + (2)) + (N : ℝ) ^ ((2) + (2)))
          * eeHermErr d N (2) (D' - 1)) ≤ (N : ℝ) ^ ε₀ / 16 * (N : ℝ)⁻¹ ^ (2) := by
        have hee0 : 0 ≤ eeHermErr d N (2) (D' - 1) := eeHermErr_nonneg d N (2) (D' - 1)
        have hstep1 : cKerShort ((2) + (2)) (Real.sqrt (min (2 - |E N|) 1))
              * ((d.W N : ℝ) ^ τ') ^ ((2) + (2)) * (N : ℝ) ^ ((2) + (2))
            ≤ cK2 * ((d.W N : ℝ) ^ τ') ^ ((2) + (2)) * (N : ℝ) ^ ((2) + (2)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hcK2_le N) (by positivity))
            (by positivity)
        have hstep2 : (cKerShort ((2) + (2)) (Real.sqrt (min (2 - |E N|) 1))
              * ((d.W N : ℝ) ^ τ') ^ ((2) + (2)) * (N : ℝ) ^ ((2) + (2))
              + (N : ℝ) ^ ((2) + (2))) * eeHermErr d N (2) (D' - 1)
            ≤ (cK2 * ((d.W N : ℝ) ^ τ') ^ ((2) + (2)) * (N : ℝ) ^ ((2) + (2))
              + (N : ℝ) ^ ((2) + (2))) * eeHermErr d N (2) (D' - 1) :=
          mul_le_mul_of_nonneg_right (add_le_add hstep1 le_rfl) hee0
        exact (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hstep2) (by positivity)).trans he3N
      have hbud := budget514 d (m := 0) (hE N) s v K N (ε := ε₀) (ε₁ := ε₁) (τ' := τ') (D' := D')
        (D_Y := D_Y) (Λ := Λ N) (Φ := Φ N) (CK := CK) q.2 (hs0 N) hlt (hv1 N) hKN1 hN1 hWN hLN hcardN
        hLWN hηN hAN hΛN (hΦ0 N) hCK0 hCKN2 hΔN' hlogN hX0 ha1N' ha2N' ha3N' he1N (he2N' (Φ N) (hΦ0 N))
        he3N' he4N (he5N _ hΔ0 hΔ)
      have hAt : AtrueN d (E N) s v K N q.1 (K N) ω q.2
          = gloop (d.L N) (d.W N) (H d s v K N (K N) ω) (zt (E N) (v N)) q.idx
            - (band d).Kval (E N) N (v N) q.idx := by
        unfold AtrueN LvalN KvN; rw [time_last s v K N (hK0 N)]; rfl
      rw [hAt] at hb
      have hfin := hb.trans hbud
      have hle : (N : ℝ) ^ ε₀ * (Λ N ^ ((1 : ℝ) / 2) + Φ N)
          * ((band d).scale (E N) N (v N) ^ (2))⁻¹ ≤ (N : ℝ) ^ ε * g := by
        rw [hg, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hNε (by linarith [hΦ0 N]))
          (by positivity)
      linarith
    -- probability
    have hbadeq : badSet (fun N (q : LoopData ((band d).L N) (2)) ω =>
          if SumZeroDyn.NonAlt q.1 then ‖SumZeroDyn.lkT (sample d) (E N) N (v N) ω q.1 q.2‖ else 0)
        (fun N _ _ => (Λ N ^ ((1 : ℝ) / 2) + Φ N) * ((band d).scale (E N) N (v N) ^ (2))⁻¹) ε N
        = Hflow d N (time s v K N (K N)) ⁻¹' Sbad := by
      rw [time_last s v K N (hK0 N)]
      ext ω
      rfl
    have hx0 : (0 : ℝ) ≤ (N : ℝ) ^ (-(D + 1)) := Real.rpow_nonneg hN0.le _
    have hGσ : ∀ σ, (Pg d) (G σ)ᶜ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))) := fun σ => by
      rw [← ofReal_measureReal]; exact ENNReal.ofReal_le_ofReal (hGP σ)
    have hcard2 : (Fintype.card {σ : Fin (2) → Bool // SumZeroDyn.NonAlt σ} : ℝ) ≤ 2 ^ (2) := by
      have h := Fintype.card_subtype_le (fun σ : Fin (2) → Bool => SumZeroDyn.NonAlt σ)
      rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at h
      exact_mod_cast h
    have hreal : (2 + (Fintype.card {σ : Fin (2) → Bool // SumZeroDyn.NonAlt σ} : ℝ))
        * (N : ℝ) ^ (-(D + 1)) ≤ (N : ℝ) ^ (-D) := by
      have hN2' : (2 : ℝ) + 2 ^ (2) ≤ N := by
        have h : ((2 ^ (2) + 2 : ℕ) : ℝ) ≤ N := by exact_mod_cast hN2N
        push_cast at h; linarith
      have e : (N : ℝ) * (N : ℝ) ^ (-(D + 1)) = (N : ℝ) ^ (-D) := by
        rw [show -(D + 1) = -D + (-1) by ring, Real.rpow_add hN0, Real.rpow_neg_one]
        field_simp
      have : (2 + (Fintype.card {σ : Fin (2) → Bool // SumZeroDyn.NonAlt σ} : ℝ))
          * (N : ℝ) ^ (-(D + 1)) ≤ (N : ℝ) * (N : ℝ) ^ (-(D + 1)) :=
        mul_le_mul_of_nonneg_right (by linarith) hx0
      linarith
    calc (band d).P (badSet _ _ ε N)
        = (P d) (Hflow d N (time s v K N (K N)) ⁻¹' Sbad) := by rw [hbadeq]; rfl
      _ = (Pg d) (H d s v K N (K N) ⁻¹' Sbad) :=
          (prob_grid_eq_flow d K N (K N) (hs0 N) (hsv N) (hK0 N) hSm).symm
      _ ≤ (Pg d) (Goodᶜ ∪ Initᶜ ∪ ⋃ σ, (G σ)ᶜ) := measure_mono hsub
      _ ≤ (Pg d) Goodᶜ + (Pg d) Initᶜ + ∑ σ, (Pg d) (G σ)ᶜ :=
          (measure_union_le _ _).trans (add_le_add (measure_union_le _ _)
            (measure_iUnion_fintype_le _ _))
      _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))) + ENNReal.ofReal ((N : ℝ) ^ (-(D + 1)))
          + ∑ _σ : {σ : Fin (2) → Bool // SumZeroDyn.NonAlt σ},
              ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))) :=
          add_le_add (add_le_add hGoodN hInitN) (Finset.sum_le_sum fun σ _ => hGσ σ)
      _ = ENNReal.ofReal ((2 + (Fintype.card {σ : Fin (2) → Bool // SumZeroDyn.NonAlt σ} : ℝ))
            * (N : ℝ) ^ (-(D + 1))) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_add (by norm_num) (by positivity), ENNReal.ofReal_natCast,
            ENNReal.ofReal_ofNat]
          ring
      _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := ENNReal.ofReal_le_ofReal hreal

end EndpointTwoN

section EndpointTwoSubtypeN

theorem endpoint_nonAlt_two_plainN {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) {E : ℕ → ℝ}
    (hEκ : ∀ N, |E N| ≤ 2 - κ) {s t : ℕ → ℝ} (hB : BoundsCoreN (sample d) E s)
    (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c)
    (hreg0 : ∀ᶠ N : ℕ in atTop, (etaT (E N) (s N) / etaT (E N) (t N)) ^ 30 ≤
      (band d).scale (E N) N (t N))
    (hAc : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale (E N) N (t N)) :
    ∀ Λ Φ : ℕ → ℝ, (∀ N, 0 ≤ Λ N) → (∀ N, 0 ≤ Φ N) →
      (∀ᶠ N : ℕ in atTop, 1 ≤ Λ N) → Lemma514PremisesN (sample d) E s t 2 Λ Φ →
      ∀ v : ℕ → ℝ, (∀ N, v N ∈ Set.Icc (s N) (t N)) →
        StochDom (band d).P
          (fun N (q : {q : LoopData ((band d).L N) 2 // q.1 0 = q.1 1}) ω =>
            ‖SumZeroDyn.lkT (sample d) (E N) N (v N) ω q.1.1 q.1.2‖)
          (fun N _ _ => (Λ N ^ ((1 : ℝ) / 2) + Φ N) * ((band d).scale (E N) N (v N) ^ 2)⁻¹) := by
  intro Λ Φ hΛ0 hΦ0 hΛ1 hprem v hv
  have h := endpoint_nonAlt_two_ite_plainN d hκ0 hκ1 hEκ hB hs0 ht1 hc0 hreg0 hAc Λ Φ hΛ0 hΦ0 hΛ1
    hprem v hv
  intro τ hτ D hD
  filter_upwards [h τ hτ D hD] with N hN
  refine le_trans (measure_mono ?_) hN
  intro ω hω
  obtain ⟨q, hq⟩ := hω
  have hna : SumZeroDyn.NonAlt q.1.1 := ⟨0, by simpa using q.2⟩
  exact ⟨q.1, by simpa [hna] using hq⟩

end EndpointTwoSubtypeN

section CompatN

end CompatN

end RBM.Gauss.Grid

end

