/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Lemma514AltEnd
import RBM1D.Flow.EnergyUniform
import RBM1D.Flow.Scales
import RBM1D.EnergyN.Gauss.Lemma514NonAlt
import RBM1D.EnergyN.Gauss.Step2Plain
import RBM1D.EnergyN.Gauss.Lemma510Fixed
import RBM1D.EnergyN.Gauss.GridAssembly
import RBM1D.EnergyN.Gauss.Lemma514Moment
import RBM1D.EnergyN.Unif.Gauss.Lemma514NonAlt

/-!
# The alternating endpoint case of Lemma 5.14 at an `N`-dependent energy

The alternating case of the endpoint estimate of Lemma 5.14 at an `N`-dependent energy
`E : ℕ → ℝ`: the `Q`-assembly (`Grid.assemblyQN`), the event bounds `Grid.ev_PYQN`,
`Grid.ev_ha2QN`, `Grid.ev_ha3QN`, and the endpoint bound for the alternating `σ` of every length
(`Grid.endpoint_alt_all_plainN`) and of length two (`Grid.endpoint_alt_two_hEndAlt_plainN`).

## The energy-dependent constants

* `ev_ha2QN`/`ev_ha3QN`: unlike the generic `ev_ha2`/`ev_ha3` of `Lemma514NonAlt` (abstract
  `mi`), these involve `(mE (E N)).im⁻¹` (resp. `(mE (E N)).im⁻¹ + 1`), which must be bounded
  before `∀ᶠ N`. They take `{κ : ℝ} (hκ0 : 0 < κ)` and `hE : ∀ N, |E N| ≤ 2 - κ`, and use the
  uniform `mκ := √(2 · min κ 1)/2 ≤ (mE (E N)).im` (`mE_im_ge`, private helper `mEIm_ge_uniQ`
  below; `min κ 1 ≤ 1 ≤ 2` discharges the side condition of `mE_im_ge`), giving
  `(mE (E N)).im⁻¹ ≤ mκ⁻¹` (`inv_anti₀`), chained through a nonnegative-factor argument.
* The constant `CK` of `endpoint_alt_all_plainN` comes from `Grid.exists_Kval_env_unif`
  (`RBM1D/EnergyN/Unif/Gauss/Lemma514NonAlt.lean`), chosen before `E`, as for
  `endpoint_nonAlt_all_plainN`; `ev_ha2QN`/`ev_ha3QN` are used inside it with the theorem's own
  `κ`, `hEκ`.
-/

noncomputable section

namespace RBM.Gauss.Grid

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.SumZeroDyn
open scoped NNReal ENNReal
open scoped Matrix.Norms.L2Operator

variable (d : Dims)

set_option maxHeartbeats 8000000 in
/-- **The `Q`-assembly at a fixed `N`**: for an alternating (non-constant) `σ`, on one event of
probability `≥ 1 - N^{-D₁}`, the frozen `Q`-process at the good-set exit satisfies the (5.91) bound
with the sharp (7.16) Case 2 weights on `A_0` and the drift, the joint `Q ⊗ Q` QV constants, the
`Y` threshold `N^{-D_Y}` and the `qErrQ` remainder. -/
theorem assemblyQN {m : ℕ} {E : ℕ → ℝ} (hE : ∀ N, |E N| < 2) (s v : ℕ → ℝ)
    (σ : Fin (m + 2) → Bool) (hσ : ∃ i j, σ i ≠ σ j)
    {ε₁ τ' D' D_Y D₁ C_P C_K : ℝ} (hε₁ : 0 < ε₁) (hτ' : 0 < τ') (hD' : 1 ≤ D')
    (hCK0 : 0 ≤ C_K) (hCK : D₁ + 4 * D_Y + ((m + 2 : ℕ) : ℝ) * 1 + 2 * C_P + 8 ≤ C_K)
    {CK : ℝ} (hCK0' : 0 ≤ CK)
    (hKenv : ∀ (N : ℕ) (u : ℝ), 0 ≤ u → u < 1 → 1 ≤ (band d).scale (E N) N u →
      (∀ J : LoopIdx (ZMod (d.L N)), J.WF → 2 ≤ J.length → J.length ≤ m + 2 →
        ‖(band d).Kval (E N) N u J‖ ≤ CK * ((band d).scale (E N) N u)⁻¹ ^ (J.length - 1))
      ∧ ∀ J : LoopIdx (ZMod (d.L N)), J.WF → J.length ≤ m + 2 → ‖(band d).Kval (E N) N u J‖ ≤ CK + 1)
    (K : ℕ → ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ (Λ Φ ℓs : ℝ), 0 ≤ Λ → 0 ≤ Φ →
      0 ≤ s N → s N < v N → v N < 1 → 1 ≤ K N → K N ≤ ⌈(N : ℝ) ^ C_K⌉₊ →
      step s v K N ≤ (N : ℝ) ^ (-C_K) → (d.L N : ℝ) ≤ (N : ℝ) ^ (1 : ℝ) →
      (∀ u, 0 ≤ u → u ≤ v N → 1 ≤ (band d).scale (E N) N u) →
      KDecayRegime d N (m + 2) τ' D' →
      PYQ d N m (v N) (etaT (E N) (v N)) ≤ (N : ℝ) ^ C_P →
      (∀ j < K N, (N : ℝ) ^ ε₁ * Λ
        + ((2 * (m + 2) + 2 : ℕ) : ℝ) * ((etaT (E N) (time s v K N (j + 1)))⁻¹ ^ (2 * (m + 2) + 2 + 1)
            * (time s v K N (j + 1) - time s v K N j))
          * ((band d).scale (E N) N (time s v K N j)) ^ (2 * (m + 2) + 2 - 1)
          ≤ 2 * (N : ℝ) ^ ε₁ * Λ) →
      (∀ j < K N, ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ 2 * (m + 2) + 2 →
        (d.W N : ℝ) ^ (-D') + (ℓ : ℝ) * ((etaT (E N) (time s v K N (j + 1)))⁻¹ ^ (ℓ + 1)
            * (time s v K N (j + 1) - time s v K N j)) ≤ (d.W N : ℝ) ^ (-(D' - 1))) →
      ∃ G : Set (Ωg d), (Pg d).real Gᶜ ≤ (N : ℝ) ^ (-D₁)
        ∧ ∀ ω ∈ G, 0 < goodExitTau514 d (E N) s v K (m + 2) ε₁ Λ Φ τ' D' ℓs N ω →
          ∀ a : LoopArg (d.L N) (m + 2),
            ‖AfrozQ d (E N) s v K N σ (goodExitTau514 d (E N) s v K (m + 2) ε₁ Λ Φ τ' D' ℓs N)
                (goodExitTau514 d (E N) s v K (m + 2) ε₁ Λ Φ τ' D' ℓs N ω) ω a‖
              ≤ kapQ (d.L N) (m + 2) (4 * (4 * (d.W N : ℝ) ^ τ')) (time s v K N) 0
                    (goodExitTau514 d (E N) s v K (m + 2) ε₁ Λ Φ τ' D' ℓs N ω)
                  * (Finset.univ.sup' Finset.univ_nonempty
                      (fun b => ‖AtrueQ d (E N) s v K N σ 0 ω b‖))
                + epsQ (d.L N) (m + 2) (time s v K N) 0
                    (goodExitTau514 d (E N) s v K (m + 2) ε₁ Λ Φ τ' D' ℓs N ω)
                  * deltaQop (d.L N) (m + 1) (4 * (d.W N : ℝ) ^ τ')
                      (MD514 d (E N) N (m + 2) (CK + 1) (time s v K N 0)) ((d.W N : ℝ) ^ (-D'))
                + step s v K N * ∑ j ∈ Finset.range
                    (goodExitTau514 d (E N) s v K (m + 2) ε₁ Λ Φ τ' D' ℓs N ω),
                    (kapQ (d.L N) (m + 2) (4 * (4 * (d.W N : ℝ) ^ τ')) (time s v K N) (j + 1)
                        (goodExitTau514 d (E N) s v K (m + 2) ε₁ Λ Φ τ' D' ℓs N ω)
                      * dDrQ d (E N) N m (time s v K N j) ε₁ τ' D' Φ CK
                          (MD514 d (E N) N (m + 2) (CK + 1) (time s v K N j)
                            * (band d).scale (E N) N (time s v K N j) ^ (m + 2))
                          (CK + 1) (MD514 d (E N) N (m + 2) (CK + 1) (time s v K N j))
                    + epsQ (d.L N) (m + 2) (time s v K N) (j + 1)
                        (goodExitTau514 d (E N) s v K (m + 2) ε₁ Λ Φ τ' D' ℓs N ω)
                      * δDQ d (E N) N m (time s v K N j) τ' D' (CK + 1)
                          (MD514 d (E N) N (m + 2) (CK + 1) (time s v K N j)) (CK + 1))
                + (N : ℝ) ^ ε₁ * Real.sqrt (∑ j ∈ Finset.range
                    (goodExitTau514 d (E N) s v K (m + 2) ε₁ Λ Φ τ' D' ℓs N ω),
                    (cQVQ d (E N) s v K N m τ' (D' - 1) (2 * (N : ℝ) ^ ε₁ * Λ)
                      (goodExitTau514 d (E N) s v K (m + 2) ε₁ Λ Φ τ' D' ℓs N ω) a j : ℝ))
                + (N : ℝ) ^ (-D_Y)
                + ∑ j ∈ Finset.range (goodExitTau514 d (E N) s v K (m + 2) ε₁ Λ Φ τ' D' ℓs N ω),
                    (1 + (1 - time s v K N
                      (goodExitTau514 d (E N) s v K (m + 2) ε₁ Λ Φ τ' D' ℓs N ω))⁻¹) ^ (m + 2)
                    * qErrQ d (E N) s v K N m (CK + 1) j := by
  filter_upwards [grid_assembly_at_tau' (μ := Pg d) (ℱ := filt d) (m + 2) hε₁ D_Y D₁ 1 C_P C_K
    hCK0 hCK] with N hN
  intro Λ Φ ℓs hΛ0 hΦ0 hs0 hsv hv1 hK1 hK hΔK hL hA1 hreg hPY hshΞ hshD
  have hn2 : 2 ≤ m + 2 := by omega
  set u := time s v K N with hu
  set Δ := step s v K N with hΔ
  set τ := goodExitTau514 d (E N) s v K (m + 2) ε₁ Λ Φ τ' D' ℓs N with hτ
  set ξ := xiOf (mSigma (E N)) σ with hξ
  set Kd : ℝ := 4 * (4 * (d.W N : ℝ) ^ τ') with hKd
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
  have hτK : ∀ ω, τ ω ≤ K N := fun ω => goodExitTau514_le d (E N) s v K (m + 2) ε₁ Λ Φ τ' D' ℓs N ω
  have hτmeas : ∀ j, MeasurableSet[filt d j] {ω | j < τ ω} :=
    fun j => lt_goodExitTau514_measurableSet d s v K (m + 2) ε₁ Λ Φ τ' D' ℓs N j
  have hmemτ : ∀ ω j, j < τ ω → H d s v K N j ω ∈ goodSet514 d (E N) N (u j) (m + 2) ε₁ Λ Φ τ' D' ℓs :=
    fun ω j h => mem_goodSet514_of_lt_goodExitTau514 d h
  have hAgrid : ∀ j ≤ K N, 1 ≤ (band d).scale (E N) N (u j) :=
    fun j hj => hA1 (u j) (hu0 j hj) (hmem j hj).2
  have hBk : ∀ j < K N, ∀ w ∈ Set.Icc (0 : ℝ) (u (j + 1)), ∀ J : LoopIdx (ZMod (d.L N)),
      J.WF → 2 ≤ J.length → J.length ≤ (m + 2) → ‖(band d).Kval (E N) N w J‖ ≤ CK + 1 := by
    intro j hj w hw J hJ h2 hln
    have hwv : w ≤ v N := hw.2.trans (hmem (j + 1) (by omega)).2
    exact (hKenv N w hw.1 (hwv.trans_lt hv1) (hA1 w hw.1 hwv)).2 J hJ hln
  have hξb : ∀ j ≤ K N, ∀ a : LoopArg (d.L N) (m + 2), ‖(u j : ℂ) * xiLoop (mSigma (E N))
      (⟨List.ofFn σ, List.ofFn a⟩ : LoopIdx (ZMod (d.L N))) ((m + 2) - 1)‖ < 1 :=
    fun j hj a => norm_time_mul_xiLoop_lt (hE N) _ _ (hu0 j hj) (hu1 j hj)
  have hstepErr : ∀ j < K N, 0 ≤ qErrQ d (E N) s v K N m (CK + 1) j
      ∧ ∀ᵐ ω ∂(Pg d), RgridQT d (E N) s v K N σ (CK + 1) j ω = RgridQ d (E N) s v K N σ j ω :=
    fun j hj => RgridQT_ae d s v K N j (E N) (hE N) hsv hj (hu0 j hj.le) (hu1 (j + 1) (by omega)) σ
      (by linarith) (hBk j hj) (hξb j hj.le)
  -- the data
  set A0 : Ωg d → LoopArg (d.L N) (m + 2) → ℂ := AtrueQ d (E N) s v K N σ 0 with hA0
  set A : ℕ → Ωg d → LoopArg (d.L N) (m + 2) → ℂ := AfrozQ d (E N) s v K N σ τ with hAdef
  set Dr : ℕ → Ωg d → LoopArg (d.L N) (m + 2) → ℂ := DgridQ d (E N) s v K N σ with hDr
  set Z : ℕ → Ωg d → LoopArg (d.L N) (m + 2) → ℂ :=
    gridZC d s v K N (m + 2) (gridΦQ d (E N) s v K N σ) with hZ
  set Y : ℕ → Ωg d → LoopArg (d.L N) (m + 2) → ℂ :=
    gridYC d s v K N (m + 2) (gridΦQ d (E N) s v K N σ) with hY
  set R : ℕ → Ωg d → LoopArg (d.L N) (m + 2) → ℂ := RgridQT d (E N) s v K N σ (CK + 1) with hR
  set κ : ℕ → ℕ → ℝ := kapQ (d.L N) (m + 2) Kd u with hκ
  set εK : ℕ → ℕ → ℝ := epsQ (d.L N) (m + 2) u with hεK
  set δ0 : ℝ := deltaQop (d.L N) (m + 1) (4 * (d.W N : ℝ) ^ τ')
    (MD514 d (E N) N (m + 2) (CK + 1) (u 0)) ((d.W N : ℝ) ^ (-D')) with hδ0
  set dDrift : ℕ → Ωg d → ℝ := fun j _ => dDrQ d (E N) N m (u j) ε₁ τ' D' Φ CK
    (MD514 d (E N) N (m + 2) (CK + 1) (u j) * (band d).scale (E N) N (u j) ^ (m + 2))
    (CK + 1) (MD514 d (E N) N (m + 2) (CK + 1) (u j)) with hdD
  set δD : ℕ → Ωg d → ℝ := fun j _ => δDQ d (E N) N m (u j) τ' D' (CK + 1)
    (MD514 d (E N) N (m + 2) (CK + 1) (u j)) (CK + 1) with hδD
  set c := cQVQ d (E N) s v K N m τ' (D' - 1) (2 * (N : ℝ) ^ ε₁ * Λ) with hc
  set vv : ℕ → ℝ := fun _ => vYQ d N m (v N) (etaT (E N) (v N)) Δ with hvv
  set ww : ℕ → ℝ := fun _ => wYQ d N m (v N) (etaT (E N) (v N)) Δ with hww
  set stepErr : ℕ → ℝ := fun j => qErrQ d (E N) s v K N m (CK + 1) j with hsE
  set PP := PYQ d N m (v N) (etaT (E N) (v N)) with hPP
  have hMK0 : 0 ≤ CK + 1 := by linarith
  have hMD0 : ∀ j ≤ K N, 0 ≤ MD514 d (E N) N (m + 2) (CK + 1) (u j) := by
    intro j hj
    unfold MD514
    have := etaT_pos (hE N) (hu1 j hj)
    positivity
  have hW4 : (1 : ℝ) ≤ 4 * (d.W N : ℝ) ^ τ' := by linarith
  have hPW : GridAssemblyHypPW (Pg d) (filt d) (d.L N) ξ u τ Δ (K N) Kd true A0 A Dr Z Y R
      κ εK δ0 dDrift δD c vv ww stepErr :=
    { hL3 := d.three_le_L N
      hξ := fun p => (norm_xiOf_mSigma (hE N).le σ p).le
      hu0 := hu0
      hu1 := hu1
      hΔ0 := hΔ0
      hexp := hexpQ d (E N) (hE N) σ s v K N hs0 hsv hv1 hK0 (Bk := CK + 1) (by linarith) hBk τ hτK
      hκ0 := fun i k hik hk => kapQ_nonneg (d.three_le_L N) (by linarith) u
        (hu0 i (hik.trans hk)) (hu1 i (hik.trans hk)) (hu0 k hk) (hu1 k hk)
      hε0 := fun i k hik hk => epsQ_nonneg (d.L N) (m + 2) u (hu1 i (hik.trans hk)) (hu1 k hk)
      hker := hker_of_Q716_sumZero (d.L N) (d.three_le_L N) hn2 (hE N) σ hu0 hmono hu1 hKd1
      hδ0 := deltaQop_nonneg (d.L N) hW4 (hMD0 0 (Nat.zero_le _)) (Real.rpow_nonneg (by positivity) _)
      hA0cls := fun ω hτ0 => kerClass_A0Q d s v K N σ ω hτ' (hu0 0 (Nat.zero_le _))
        (hu1 0 (Nat.zero_le _)) (hmemτ ω 0 hτ0) (hMD0 0 (Nat.zero_le _))
        (fun J hJ hln => norm_lk_env d (hE N) (H_isHermitian d s v K N 0 ω) (hu0 0 (Nat.zero_le _))
          (hu1 0 (Nat.zero_le _)) (hKenv N (u 0) (hu0 0 (Nat.zero_le _)) (hu1 0 (Nat.zero_le _))
            (hAgrid 0 (Nat.zero_le _))).2 J hJ hln)
      hdDrift0 := fun ω j hj => dDrQ_nonneg d (hE N) N m (hu0 j hj.le) (hu1 j hj.le)
        (lt_of_lt_of_le one_pos (hAgrid j hj.le)) hΦ0 hCK0'
        (mul_nonneg (hMD0 j hj.le) (pow_nonneg (le_trans zero_le_one (hAgrid j hj.le)) _))
        hMK0 (hMD0 j hj.le)
      hδD0 := fun ω j hj => δDQ_nonneg d (hE N) N m (hu0 j hj.le) (hu1 j hj.le) hτ'.le hMK0
        (hMD0 j hj.le) hMK0
      hdrift := fun ω j hj hjτ b => norm_DgridQ_le d (hE N) s v K N σ hσ j ω hτ' (by linarith) hΦ0
        (hu0 j hj.le) (hu1 j hj.le) (hAgrid j hj.le) hreg (hmemτ ω j hjτ) hCK0'
        (hKenv N (u j) (hu0 j hj.le) (hu1 j hj.le) (hAgrid j hj.le)).1
        (mul_nonneg (hMD0 j hj.le) (pow_nonneg (le_trans zero_le_one (hAgrid j hj.le)) _))
        (fun m' _ hm' => xiLKM_crude d (hE N) (H_isHermitian d s v K N j ω) (hu0 j hj.le)
          (hu1 j hj.le) (hAgrid j hj.le)
          (hKenv N (u j) (hu0 j hj.le) (hu1 j hj.le) (hAgrid j hj.le)).2 hm')
        hMK0 (hMD0 j hj.le) (hKenv N (u j) (hu0 j hj.le) (hu1 j hj.le) (hAgrid j hj.le)).2
        (fun J hJ hln => norm_lk_env d (hE N) (H_isHermitian d s v K N j ω) (hu0 j hj.le)
          (hu1 j hj.le) (hKenv N (u j) (hu0 j hj.le) (hu1 j hj.le) (hAgrid j hj.le)).2 J hJ hln) b
      hDcls := fun ω j hj hjτ => kerClass_DgridQ d (hE N) s v K N σ j ω hτ' (by linarith)
        (hu0 j hj.le) (hmono j (j + 1) (by omega) (by omega)) (hu1 (j + 1) (by omega)) hreg
        (hmemτ ω j hjτ) hMK0 (hMD0 j hj.le) hMK0
        (hKenv N (u j) (hu0 j hj.le) (hu1 j hj.le) (hAgrid j hj.le)).2
        (fun J hJ _ hln => (hKenv N (u j) (hu0 j hj.le) (hu1 j hj.le) (hAgrid j hj.le)).2 J hJ hln)
        (fun J hJ hln => norm_lk_env d (hE N) (H_isHermitian d s v K N j ω) (hu0 j hj.le)
          (hu1 j hj.le) (hKenv N (u j) (hu0 j hj.le) (hu1 j hj.le) (hAgrid j hj.le)).2 J hJ hln)
      hc_pos := cQVQ_sum_pos d (hE N) s v K N hs0 hsv hv1 (by positivity)
      hYmeas := stronglyMeasurable_gridYC d s v K N (m + 2) (gridΦQ d (E N) s v K N σ)
        (gridΦQ_testFun d (hE N) hsv.le hv1 hK0 σ)
      hv0 := fun j _ => by
        show 0 ≤ vYQ d N m (v N) (etaT (E N) (v N)) Δ
        unfold vYQ
        have := xMom_nonneg d N 2; have := xMom_nonneg d N 4
        positivity
      hw0 := fun j _ => by
        show 0 ≤ wYQ d N m (v N) (etaT (E N) (v N)) Δ
        unfold wYQ
        have := xMom_nonneg d N 2; have := xMom_nonneg d N 8
        have : 0 ≤ cYQ d N m (v N) (etaT (E N) (v N)) Δ ^ 4 := by positivity
        positivity
      hYmeanRe := fun k hk b j hj =>
        (Y_fieldsQ d (hE N) s v K N hs0 hsv.le hv1 hK0 σ τ hτmeas k hk b j hj).1
      hYmeanIm := fun k hk b j hj =>
        (Y_fieldsQ d (hE N) s v K N hs0 hsv.le hv1 hK0 σ τ hτmeas k hk b j hj).2.1
      hYintRe := fun k hk b j hj =>
        (Y_fieldsQ d (hE N) s v K N hs0 hsv.le hv1 hK0 σ τ hτmeas k hk b j hj).2.2.1
      hYintIm := fun k hk b j hj =>
        (Y_fieldsQ d (hE N) s v K N hs0 hsv.le hv1 hK0 σ τ hτmeas k hk b j hj).2.2.2.1
      hYcondRe := fun k hk b j hj =>
        (Y_fieldsQ d (hE N) s v K N hs0 hsv.le hv1 hK0 σ τ hτmeas k hk b j hj).2.2.2.2.1
      hYcondIm := fun k hk b j hj =>
        (Y_fieldsQ d (hE N) s v K N hs0 hsv.le hv1 hK0 σ τ hτmeas k hk b j hj).2.2.2.2.2.1
      hY4Re := fun k hk b j hj =>
        (Y_fieldsQ d (hE N) s v K N hs0 hsv.le hv1 hK0 σ τ hτmeas k hk b j hj).2.2.2.2.2.2.1
      hY4Im := fun k hk b j hj =>
        (Y_fieldsQ d (hE N) s v K N hs0 hsv.le hv1 hK0 σ τ hτmeas k hk b j hj).2.2.2.2.2.2.2
      hstepErr0 := fun j hj => (hstepErr j hj).1
      hR := fun ω j hj _ b => norm_RgridQT_le d (E N) s v K N σ (CK + 1) j (hstepErr j hj).1 ω b }
  have hqv := hqvQ d (hE N) s v K N σ hs0 hsv.le hv1 hK0 τ hτmeas (Φq := 2 * (N : ℝ) ^ ε₁ * Λ)
    (D'' := D' - 1) hτ'.le hmemτ hAgrid hshΞ (fun j hj ℓ h1 h2 => by
      have := hshD j hj ℓ h1 h2
      simpa [neg_sub] using this)
  have hZmeas := stronglyMeasurable_gridZC s v K N (m + 2) (gridΦQ d (E N) s v K N σ)
    (gridΦQ_testFun d (hE N) hsv.le hv1 hK0 σ)
  have hKΔ : (K N : ℝ) * Δ ≤ 1 := by
    have hKpos : (0 : ℝ) < K N := by exact_mod_cast (by omega : 0 < K N)
    rw [hΔ]; unfold step
    rw [mul_div_cancel₀ _ hKpos.ne']
    linarith [hs0, hv1]
  have hP0 : 0 ≤ PP := by
    rw [hPP]; unfold PYQ
    have := xMom_nonneg d N 2; have := xMom_nonneg d N 4; have := xMom_nonneg d N 8
    positivity
  have hvw := vYQ_wYQ_le d N m (v N) (etaT (E N) (v N)) Δ
  exact hN (K N) (d.L N) hK1 hK hL ξ u τ Δ Kd true A0 A Dr Z Y R κ εK δ0 dDrift δD c vv ww
    stepErr PP hΔK hKΔ hP0 hPY (fun j _ => hvw.1) (fun j _ => hvw.2) hτmeas hZmeas hqv hPW hτK


theorem ev_PYQN (m : ℕ) {C_P : ℝ} (hCP : ((10 * m + 24 : ℕ) : ℝ) < C_P) {E : ℕ → ℝ} (hE : ∀ N, |E N| < 2)
    {v : ℕ → ℝ} (hv1 : ∀ N, v N < 1) (hη : ∀ᶠ N : ℕ in atTop, (etaT (E N) (v N))⁻¹ ≤ N) :
    ∀ᶠ N : ℕ in atTop, PYQ d N m (v N) (etaT (E N) (v N)) ≤ (N : ℝ) ^ C_P := by
  filter_upwards [ev_dims514 d, hη, ev_rpow_le hCP (3428 * 32 ^ (2 * (m + 2)) * ((m + 2 : ℕ) : ℝ) ^ 4)]
    with N hd hηN hA
  obtain ⟨hN1, -, -, hL, -, hcard, -⟩ := hd
  have h := PYQ_le d N m hN1 hcard hL (hv1 N) (inv_eta_le_of (hE N) (hv1 N) hηN le_rfl).2
    (etaT_pos (hE N) (hv1 N)) hηN
  rw [natpow_eq_rpow (N : ℝ) (10 * m + 24)] at h
  exact h.trans hA

section AbsorbMainQN

open Real

/-! ### A private helper

`mE_im_ge` (`Flow/Scales.lean`) needs its `κ`-argument to satisfy `κ ≤ 2`; `ev_ha2QN`/`ev_ha3QN`
only assume `0 < κ` (no upper bound), so both go through `κ' := min κ 1 ≤ 1 ≤ 2`. -/

private theorem mEIm_ge_uniQ {κ : ℝ} (hκ0 : 0 < κ) {E : ℝ} (hEκ : |E| ≤ 2 - κ) :
    Real.sqrt (2 * min κ 1) / 2 ≤ (mE E).im := by
  have hκ'0 : 0 < min κ 1 := lt_min hκ0 one_pos
  have hκ'2 : min κ 1 ≤ 2 := (min_le_right κ 1).trans one_le_two
  have hEκ' : |E| ≤ 2 - min κ 1 := hEκ.trans (by linarith [min_le_left κ 1])
  exact mE_im_ge hκ'0 hκ'2 hEκ'

set_option maxHeartbeats 1600000 in
/-- (ha2Q) The drift main term, with the `log N` of `Σ Δ/η`, energy-uniform via `κ`: the
constant `(mE (E N)).im⁻¹` is bounded by the uniform `mκ⁻¹`. -/
theorem ev_ha2QN (m : ℕ) {ε ε₁ τ' CK : ℝ} (hτ' : 0 ≤ τ') (hε₁ : 0 ≤ ε₁) (hCK : 0 ≤ CK)
    {κ : ℝ} (hκ0 : 0 < κ) {E : ℕ → ℝ} (hE : ∀ N, |E N| ≤ 2 - κ)
    (hε : ((3 * m + 6 : ℕ) : ℝ) * τ' + 2 * ε₁ < ε) :
    ∀ᶠ N : ℕ in atTop, cKerSumZero (m + 2) * (4 * (4 * (d.W N : ℝ) ^ τ')) ^ (2 * (m + 2))
      * McQ d N m ε₁ τ' CK * ((mE (E N)).im⁻¹ * Real.log N) ≤ (N : ℝ) ^ ε / 16 := by
  set mκ := Real.sqrt (2 * min κ 1) / 2 with hmκ
  have hmκpos : 0 < mκ := by
    have h1 : 0 < min κ 1 := lt_min hκ0 one_pos
    rw [hmκ]; positivity
  set M0 := 4 * exp 1 * ((m + 2 : ℕ) : ℝ) + ((Finset.Icc 3 (m + 2)).card : ℝ)
      * (8 * exp 1 * ((m + 2 : ℕ) : ℝ) ^ 2 * CK) + 4 * exp 1 * ((m + 2 : ℕ) : ℝ) ^ 2 with hM0
  have hc := cTwo52_pos
  have hM00 : 0 ≤ M0 := by rw [hM0]; positivity
  set C1 := (1 + (24 * exp 1 * cTwo52) ^ (m + 1)) * M0 + 4 * ((m : ℝ) + 2) * cTwo52 ^ (m + 1)
    * (4 * exp 1) ^ m with hC1
  have hC10 : 0 ≤ C1 := by rw [hC1]; positivity
  set C := cKerSumZero (m + 2) * 16 ^ (2 * (m + 2)) * C1 * mκ⁻¹ with hC
  have hC0 : 0 ≤ C := by rw [hC]; have := cKerSumZero_nonneg (m + 2); positivity
  filter_upwards [ev_dims514 d, ev_rpow_log_le hε (16 * C)] with N hd hA
  obtain ⟨hN1, -, hWN, -, -, -, -⟩ := hd
  have hN0 : (0 : ℝ) < N := by linarith
  have hlog0 : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hmiN : (mE (E N)).im⁻¹ ≤ mκ⁻¹ := inv_anti₀ hmκpos (mEIm_ge_uniQ hκ0 (hE N))
  set w := (d.W N : ℝ) ^ τ' with hw
  have hw1 : 1 ≤ w := Real.one_le_rpow (by exact_mod_cast d.W_pos N) hτ'
  have hNe1 : 1 ≤ (N : ℝ) ^ ε₁ := Real.one_le_rpow hN1 hε₁
  have hMc := Mc514_le d (n := m + 2) (CK := CK) hN1 hWN hτ' hε₁ hCK
  rw [← hM0] at hMc
  have hMc0 : 0 ≤ Mc514 d N (m + 2) ε₁ τ' CK := by
    unfold Mc514
    have := Real.rpow_nonneg (Nat.cast_nonneg (α := ℝ) (d.W N)) τ'
    have := Real.rpow_nonneg hN0.le ε₁
    positivity
  have hG := G_le_w d (N := N) (m := m) hτ'
  rw [← hw] at hG
  have hNτ : 1 ≤ (N : ℝ) ^ (τ' + 2 * ε₁) := Real.one_le_rpow hN1 (by linarith)
  have hNε : (N : ℝ) ^ ε₁ ≤ (N : ℝ) ^ (τ' + 2 * ε₁) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hwm : w ^ m ≤ w ^ (m + 1) := pow_le_pow_right₀ hw1 (by omega)
  have hMcQ : McQ d N m ε₁ τ' CK ≤ C1 * w ^ (m + 1) * (N : ℝ) ^ (τ' + 2 * ε₁) := by
    unfold McQ
    rw [← hw]
    have t1 : (1 + (6 * exp 1 * cTwo52 * (4 * w)) ^ (m + 1)) * Mc514 d N (m + 2) ε₁ τ' CK
        ≤ ((1 + (24 * exp 1 * cTwo52) ^ (m + 1)) * w ^ (m + 1)) * (M0 * (N : ℝ) ^ (τ' + 2 * ε₁)) :=
      mul_le_mul hG hMc hMc0 (by positivity)
    have t2 : 4 * ((m : ℝ) + 2) * cTwo52 ^ (m + 1) * (4 * exp 1) ^ m * w ^ m * (N : ℝ) ^ ε₁
        ≤ 4 * ((m : ℝ) + 2) * cTwo52 ^ (m + 1) * (4 * exp 1) ^ m * w ^ (m + 1)
          * (N : ℝ) ^ (τ' + 2 * ε₁) := by gcongr
    have e : C1 * w ^ (m + 1) * (N : ℝ) ^ (τ' + 2 * ε₁)
        = ((1 + (24 * exp 1 * cTwo52) ^ (m + 1)) * w ^ (m + 1)) * (M0 * (N : ℝ) ^ (τ' + 2 * ε₁))
          + 4 * ((m : ℝ) + 2) * cTwo52 ^ (m + 1) * (4 * exp 1) ^ m * w ^ (m + 1)
            * (N : ℝ) ^ (τ' + 2 * ε₁) := by rw [hC1]; ring
    rw [e]; linarith
  have hK : (4 * (4 * w)) ^ (2 * (m + 2)) = 16 ^ (2 * (m + 2)) * w ^ (2 * (m + 2)) := by
    rw [← mul_pow]; ring_nf
  have hwp := wpow_le d (N := N) hτ' hWN (3 * m + 5)
  rw [← hw] at hwp
  have hcS := cKerSumZero_nonneg (m + 2)
  have hMcQ0 : 0 ≤ McQ d N m ε₁ τ' CK := McQ_nonneg d N m hCK
  calc cKerSumZero (m + 2) * (4 * (4 * w)) ^ (2 * (m + 2)) * McQ d N m ε₁ τ' CK
        * ((mE (E N)).im⁻¹ * Real.log N)
      ≤ cKerSumZero (m + 2) * (4 * (4 * w)) ^ (2 * (m + 2)) * McQ d N m ε₁ τ' CK
        * (mκ⁻¹ * Real.log N) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hmiN hlog0) (by positivity)
    _ ≤ cKerSumZero (m + 2) * (16 ^ (2 * (m + 2)) * w ^ (2 * (m + 2)))
        * (C1 * w ^ (m + 1) * (N : ℝ) ^ (τ' + 2 * ε₁)) * (mκ⁻¹ * Real.log N) := by
        rw [hK]; gcongr
    _ = C * w ^ (3 * m + 5) * (N : ℝ) ^ (τ' + 2 * ε₁) * Real.log N := by
        rw [hC, show 3 * m + 5 = 2 * (m + 2) + (m + 1) by ring, pow_add]; ring
    _ ≤ C * (N : ℝ) ^ (((3 * m + 5 : ℕ) : ℝ) * τ') * (N : ℝ) ^ (τ' + 2 * ε₁) * Real.log N := by
        gcongr
    _ = C * (N : ℝ) ^ (((3 * m + 6 : ℕ) : ℝ) * τ' + 2 * ε₁) * Real.log N := by
        rw [mul_assoc C, ← Real.rpow_add hN0]; congr 3; push_cast; ring
    _ ≤ (16 * C * (N : ℝ) ^ (((3 * m + 6 : ℕ) : ℝ) * τ' + 2 * ε₁) * (Real.log N + 1)) / 16 := by
        have : 0 ≤ C * (N : ℝ) ^ (((3 * m + 6 : ℕ) : ℝ) * τ' + 2 * ε₁) := by positivity
        nlinarith
    _ ≤ (N : ℝ) ^ ε / 16 := by linarith

set_option maxHeartbeats 1600000 in
/-- (ha3Q) The QV main term, energy-uniform via `κ`: the constant `(mE (E N)).im⁻¹ + 1` is
bounded by the uniform `mκ⁻¹ + 1`. -/
theorem ev_ha3QN (m : ℕ) {ε ε₁ τ' : ℝ} (hτ' : 0 < τ') (hτ'1 : τ' ≤ 1) (hε₁ : 0 ≤ ε₁)
    {κ : ℝ} (hκ0 : 0 < κ) {E : ℕ → ℝ} (hE : ∀ N, |E N| ≤ 2 - κ)
    (hε : ((6 * m + 11 : ℕ) : ℝ) * τ' + ε₁ < 2 * ε - 2 * ε₁) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ ε₁ * Real.sqrt (QVmain d (E N) N m ε₁ τ') ≤ (N : ℝ) ^ ε / 16 := by
  have hc := cTwo52_pos
  set mκ := Real.sqrt (2 * min κ 1) / 2 with hmκ
  have hmκpos : 0 < mκ := by
    have h1 : 0 < min κ 1 := lt_min hκ0 one_pos
    rw [hmκ]; positivity
  set CP := (1 + (6 * exp 1 * cTwo52) ^ (m + 1)) * (1 + (8 * exp 1 * cTwo52) ^ (m + 1)) + 1 with hCP
  have hCP0 : 0 ≤ CP := by rw [hCP]; positivity
  set C := cKerSumZero ((m + 1 + 1) + (m + 1 + 1)) * 4 ^ (2 * ((m + 1 + 1) + (m + 1 + 1))) * CP
    * (12 * exp 1 * ((m + 1 + 1 : ℕ) : ℝ) ^ 2) * (mκ⁻¹ + 1) with hC
  have hC0 : 0 ≤ C := by
    rw [hC]; have := cKerSumZero_nonneg ((m + 1 + 1) + (m + 1 + 1)); positivity
  filter_upwards [ev_dims514 d, ev_qqCoefTail d (m + 1) hτ' hτ'1, ev_rpow_log_le hε (256 * C)]
    with N hd hT hA
  obtain ⟨hN1, -, hWN, -, -, -, -⟩ := hd
  have hN0 : (0 : ℝ) < N := by linarith
  have hlog0 : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hmiN : (mE (E N)).im⁻¹ ≤ mκ⁻¹ := inv_anti₀ hmκpos (mEIm_ge_uniQ hκ0 (hE N))
  have hmiN0 : 0 < (mE (E N)).im := mE_im_pos (by linarith [hE N])
  set w := (d.W N : ℝ) ^ τ' with hw
  have hw1 : 1 ≤ w := Real.one_le_rpow (by exact_mod_cast d.W_pos N) hτ'.le
  have hqE : qqCoefE (d.L N) (m + 1) w ≤ CP * w ^ (2 * (m + 1)) := by
    unfold qqCoefE qqCoefPoly
    have h1 : 1 + (6 * exp 1 * cTwo52 * w) ^ (m + 1) ≤ (1 + (6 * exp 1 * cTwo52) ^ (m + 1)) * w ^ (m + 1) := by
      rw [mul_pow]
      have := one_le_pow₀ (n := m + 1) hw1
      nlinarith [pow_nonneg (by positivity : (0 : ℝ) ≤ 6 * exp 1 * cTwo52) (m + 1)]
    have h2 : 1 + (8 * exp 1 * cTwo52 * w) ^ (m + 1) ≤ (1 + (8 * exp 1 * cTwo52) ^ (m + 1)) * w ^ (m + 1) := by
      rw [mul_pow]
      have := one_le_pow₀ (n := m + 1) hw1
      nlinarith [pow_nonneg (by positivity : (0 : ℝ) ≤ 8 * exp 1 * cTwo52) (m + 1)]
    have h12 := mul_le_mul h1 h2 (by positivity) (by positivity)
    have hw2 : 1 ≤ w ^ (2 * (m + 1)) := one_le_pow₀ hw1
    have e : (1 + (6 * exp 1 * cTwo52) ^ (m + 1)) * w ^ (m + 1)
        * ((1 + (8 * exp 1 * cTwo52) ^ (m + 1)) * w ^ (m + 1))
        = (1 + (6 * exp 1 * cTwo52) ^ (m + 1)) * (1 + (8 * exp 1 * cTwo52) ^ (m + 1))
          * w ^ (2 * (m + 1)) := by rw [two_mul, pow_add]; ring
    rw [hCP]
    nlinarith
  have hwp := wpow_le d (N := N) hτ'.le hWN (6 * m + 11)
  rw [← hw] at hwp
  have hNe0 : 0 ≤ (N : ℝ) ^ ε₁ := Real.rpow_nonneg hN0.le _
  have hQ : QVmain d (E N) N m ε₁ τ' ≤ C * (N : ℝ) ^ (((6 * m + 11 : ℕ) : ℝ) * τ' + ε₁) * (Real.log N + 1) := by
    unfold QVmain
    rw [← hw]
    have hl : (mE (E N)).im⁻¹ * Real.log N + 1 ≤ (mκ⁻¹ + 1) * (Real.log N + 1) := by
      have h0 : 0 ≤ mκ⁻¹ := (inv_pos.mpr hmκpos).le
      have h0' : 0 ≤ (mE (E N)).im⁻¹ := (inv_pos.mpr hmiN0).le
      nlinarith [mul_le_mul_of_nonneg_right hmiN hlog0]
    have hcS := cKerSumZero_nonneg ((m + 1 + 1) + (m + 1 + 1))
    have hqE0 : 0 ≤ qqCoefE (d.L N) (m + 1) w := qqCoefE_nonneg _ _ (by linarith)
    have h4w : (4 * w) ^ (2 * ((m + 1 + 1) + (m + 1 + 1)))
        = 4 ^ (2 * ((m + 1 + 1) + (m + 1 + 1))) * w ^ (2 * ((m + 1 + 1) + (m + 1 + 1))) := by
      rw [mul_pow]
    calc cKerSumZero ((m + 1 + 1) + (m + 1 + 1)) * (4 * w) ^ (2 * ((m + 1 + 1) + (m + 1 + 1)))
          * qqCoefE (d.L N) (m + 1) w
          * (6 * exp 1 * ((m + 1 + 1 : ℕ) : ℝ) ^ 2 * w * (2 * (N : ℝ) ^ ε₁))
          * ((mE (E N)).im⁻¹ * Real.log N + 1)
        ≤ cKerSumZero ((m + 1 + 1) + (m + 1 + 1)) * (4 ^ (2 * ((m + 1 + 1) + (m + 1 + 1)))
            * w ^ (2 * ((m + 1 + 1) + (m + 1 + 1))))
          * (CP * w ^ (2 * (m + 1)))
          * (6 * exp 1 * ((m + 1 + 1 : ℕ) : ℝ) ^ 2 * w * (2 * (N : ℝ) ^ ε₁))
          * ((mκ⁻¹ + 1) * (Real.log N + 1)) := by
          rw [h4w]; gcongr
      _ = C * (w ^ (2 * ((m + 1 + 1) + (m + 1 + 1))) * w ^ (2 * (m + 1)) * w) * (N : ℝ) ^ ε₁
          * (Real.log N + 1) := by rw [hC]; ring
      _ = C * w ^ (6 * m + 11) * (N : ℝ) ^ ε₁ * (Real.log N + 1) := by
          rw [← pow_add, ← pow_succ,
            show 2 * ((m + 1 + 1) + (m + 1 + 1)) + 2 * (m + 1) + 1 = 6 * m + 11 by ring]
      _ ≤ C * (N : ℝ) ^ (((6 * m + 11 : ℕ) : ℝ) * τ') * (N : ℝ) ^ ε₁ * (Real.log N + 1) := by
          gcongr
      _ = _ := by rw [mul_assoc C, ← Real.rpow_add hN0]
  have hsq : Real.sqrt (QVmain d (E N) N m ε₁ τ') ≤ (N : ℝ) ^ (ε - ε₁) / 16 := by
    rw [Real.sqrt_le_left (by positivity)]
    have e : ((N : ℝ) ^ (ε - ε₁) / 16) ^ 2 = (N : ℝ) ^ (2 * ε - 2 * ε₁) / 256 := by
      rw [div_pow, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num; ring_nf
    rw [e]
    linarith
  calc (N : ℝ) ^ ε₁ * Real.sqrt (QVmain d (E N) N m ε₁ τ')
      ≤ (N : ℝ) ^ ε₁ * ((N : ℝ) ^ (ε - ε₁) / 16) := mul_le_mul_of_nonneg_left hsq hNe0
    _ = (N : ℝ) ^ ε / 16 := by rw [mul_div_assoc', ← Real.rpow_add hN0]; ring_nf

end AbsorbMainQN

set_option maxHeartbeats 16000000 in
-- a long proof; raise the heartbeat limit
/-- **The endpoint bound for the alternating `σ`**: for loops of length `m + 2`, under the premises
`Lemma514PremisesN` with `Λ ≥ 1` eventually, `‖lkT‖ ≺ (Λ^{1/2} + Φ) (W ℓ_v η_v)^{-(m+2)}` at
the alternating `σ` and every time `v ∈ [s, t]`. The constants of `ev_ha2QN`/`ev_ha3QN` are used
with this theorem's own `κ`, `hEκ`; `CK` comes from `Grid.exists_Kval_env_unif`. -/
theorem endpoint_alt_all_plainN {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) {E : ℕ → ℝ} (hEκ : ∀ N, |E N| ≤ 2 - κ)
    {s t : ℕ → ℝ} (hB : BoundsCoreN (sample d) E s) (hs0 : ∀ N, 0 ≤ s N)
    (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c)
    (hreg0 : ∀ᶠ N : ℕ in atTop, (etaT (E N) (s N) / etaT (E N) (t N)) ^ 30 ≤
      (band d).scale (E N) N (t N))
    (hAc : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale (E N) N (t N)) :
    ∀ m : ℕ, ∀ Λ Φ : ℕ → ℝ, (∀ N, 0 ≤ Λ N) → (∀ N, 0 ≤ Φ N) →
      (∀ᶠ N : ℕ in atTop, 1 ≤ Λ N) → Lemma514PremisesN (sample d) E s t (m + 2) Λ Φ →
      ∀ v : ℕ → ℝ, (∀ N, v N ∈ Set.Icc (s N) (t N)) →
        StochDom (band d).P
          (fun N (q : LoopData ((band d).L N) (m + 2)) ω =>
            if q.1 = sigmaAltGen (m + 2) ∨ q.1 = sigmaAltGen' (m + 2)
            then ‖SumZeroDyn.lkT (sample d) (E N) N (v N) ω q.1 q.2‖ else 0)
          (fun N _ _ => (Λ N ^ ((1 : ℝ) / 2) + Φ N) * ((band d).scale (E N) N (v N) ^ (m + 2))⁻¹) := by
  intro m Λ Φ hΛ0 hΦ0 hΛ1 hprem v hv
  have hE : ∀ N, |E N| < 2 := fun N => by linarith [hEκ N]
  have hsv : ∀ N, s N ≤ v N := fun N => (hv N).1
  have hvt : ∀ N, v N ≤ t N := fun N => (hv N).2
  have hv1 : ∀ N, v N < 1 := fun N => (hvt N).trans_lt (ht1 N)
  obtain ⟨hreg0_v, hAc_v⟩ := hreg_sub514_plainN d hE hsv hvt ht1 hreg0 hAc
  have hcond_v : Cond272N (band d) E s v := Step2.cond272_of_plainN hE hsv hv1 hreg0_v
  obtain ⟨CK, hCK0, hKenv0⟩ := exists_Kval_env_unif d hκ0 hκ1 (m + 2) (by omega)
  have hKenv := fun (N : ℕ) (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u < 1)
      (hA1 : 1 ≤ (band d).scale (E N) N u) => hKenv0 (E N) (hEκ N) N u hu0 hu1 hA1
  obtain ⟨hP1, hP2, hP3, hP4⟩ := hprem
  intro ε hε D hD
  -- the exponents, functions of `(ε, D, n)` only
  set nR : ℝ := ((m + 2 : ℕ) : ℝ) with hnR
  have hnRm : nR = (m : ℝ) + 2 := by rw [hnR]; push_cast; ring
  have hnR2 : (2 : ℝ) ≤ nR := by rw [hnRm]; have := (Nat.cast_nonneg m : (0 : ℝ) ≤ m); linarith
  set ε₀ : ℝ := min ε 1 with hε₀
  have hε₀0 : 0 < ε₀ := lt_min hε one_pos
  have hε₀1 : ε₀ ≤ 1 := min_le_right _ _
  have hε₀ε : ε₀ ≤ ε := min_le_left _ _
  set ε₁ : ℝ := ε₀ / 8 with hε₁
  set τ' : ℝ := ε₀ / (16 * (3 * nR + 1)) with hτ'
  set D' : ℝ := 50 * nR + 100 with hD'
  set D_Y : ℝ := ((2 * (m + 2) + 3 : ℕ) : ℝ) with hD_Y
  set C_P : ℝ := 10 * nR + 5 with hC_P
  set C_K : ℝ := (D + 1) + 4 * D_Y + nR * 1 + 2 * C_P + 8 + D' + 20 * nR + 100 with hC_K
  set K : ℕ → ℕ := Kc C_K with hK
  have hε₁0 : 0 < ε₁ := by rw [hε₁]; linarith
  have hε₁1 : ε₁ ≤ 1 := by rw [hε₁]; linarith
  have hden : 0 < 16 * (3 * nR + 1) := by linarith
  have hτ'0 : 0 < τ' := by rw [hτ']; exact div_pos hε₀0 hden
  have hτeq : τ' * (16 * (3 * nR + 1)) = ε₀ := by rw [hτ']; field_simp
  have hτ'1 : τ' ≤ 1 := by nlinarith
  have hD_Yv : D_Y = 2 * nR + 3 := by rw [hD_Y, hnRm]; push_cast; ring
  have hC_K0 : 0 ≤ C_K := by rw [hC_K, hD_Yv]; nlinarith
  have hK0 : ∀ N, K N ≠ 0 := Kc_ne_zero C_K
  have hKcard := ev_Kcard C_K hC_K0
  have hC1 : (0 : ℝ) ≤ C_K + 1 := by linarith
  -- the four grid premises (flow → grid)
  have hYΛ : StochDom (Pg d) (fun N (k : Fin (K N + 1)) ω =>
      xiLM d (E N) N (time s v K N k) (H d s v K N k ω) (2 * (m + 2) + 2)) (fun N _ _ => Λ N) :=
    stochDom_grid_of_flow514 d K hs0 hsv hvt hK0 hC1 hKcard
      (fun N u M => xiLM d (E N) N u M (2 * (m + 2) + 2)) (fun N u => measurable_xiLM d (E N) N u _) Λ hP1
  have hXΦlt : ∀ m', 1 ≤ m' → m' < m + 2 → StochDom (Pg d) (fun N (k : Fin (K N + 1)) ω =>
      xiLKM d (E N) N (time s v K N k) (H d s v K N k ω) m') (fun N _ _ => Φ N) := fun m' h1 h2 =>
    stochDom_grid_of_flow514 d K hs0 hsv hvt hK0 hC1 hKcard
      (fun N u M => xiLKM d (E N) N u M m') (fun N u => measurable_xiLKM d (E N) N u _) Φ (hP2 m' h1 h2)
  have hXΦprod : ∀ m', 2 ≤ m' → m' ≤ m + 2 → StochDom (Pg d) (fun N (k : Fin (K N + 1)) ω =>
      xiLKM d (E N) N (time s v K N k) (H d s v K N k ω) m'
        * xiLKM d (E N) N (time s v K N k) (H d s v K N k ω) (m + 2 - m' + 2)
        / (band d).scale (E N) N (time s v K N k)) (fun N _ _ => Φ N) := fun m' h1 h2 => by
    have h := stochDom_grid_of_flow514 d K hs0 hsv hvt hK0 hC1 hKcard
      (fun N u M => xiLKM d (E N) N u M m' * xiLKM d (E N) N u M (m + 2 - m' + 2) * ((band d).scale (E N) N u)⁻¹)
      (fun N u => ((measurable_xiLKM d (E N) N u _).mul (measurable_xiLKM d (E N) N u _)).mul_const _) Φ
      (hP3 m' h1 h2)
    simpa only [div_eq_mul_inv] using h
  have hYΦ : StochDom (Pg d) (fun N (k : Fin (K N + 1)) ω =>
      xiLM d (E N) N (time s v K N k) (H d s v K N k ω) (m + 2 + 1)) (fun N _ _ => Φ N) :=
    stochDom_grid_of_flow514 d K hs0 hsv hvt hK0 hC1 hKcard
      (fun N u M => xiLM d (E N) N u M (m + 2 + 1)) (fun N u => measurable_xiLM d (E N) N u _) Φ hP4
  have hGood := highProb_grid_goodSet514_plainN d hκ0 hκ1 hEκ hB hs0 hsv hv1 hcond_v hc0 hreg0_v
    hAc_v K hK0 hC1 hKcard (m + 2) hτ'0 (D := D') (by rw [hD']; linarith) hε₁0 Λ Φ hYΛ hXΦlt
    hXΦprod hYΦ
  -- the assembly, for each of the two alternating charges
  have hCKc : (D + 1) + 4 * D_Y + ((m + 2 : ℕ) : ℝ) * 1 + 2 * C_P + 8 ≤ C_K := by
    rw [hC_K, ← hnR]; linarith
  have hasm := fun σ : {σ : Fin (m + 2) → Bool // IsAltQ m σ} =>
    assemblyQN d hE s v σ.1 σ.2.nonconst (D' := D') (D_Y := D_Y) (D₁ := D + 1) (C_P := C_P)
      (C_K := C_K) hε₁0 hτ'0 (by rw [hD']; linarith) hC_K0 hCKc hCK0 hKenv K
  have hasmAll := Filter.eventually_all.2 hasm
  -- the remaining eventual facts
  set q : ℕ := 2 * (m + 2) + 2 with hq
  have hPTD : 2 * (((PT m : ℕ) : ℝ) + (q : ℝ) + 1) ≤ D' - 1 := by
    rw [hD', hnRm, hq]; unfold PT; push_cast; nlinarith
  have hPTD' : 2 * (((PT m : ℕ) : ℝ) + (q : ℝ) + 1) ≤ D' := by linarith
  have hInit := ev_init514N d hB (n := m + 2) (by omega) hs0 hsv K hK0 hε₁0 (D := D + 1) (by linarith)
  have hlog := sum_step_div_eta_le_plainN d hE hs0 hsv hv1 hc0 hreg0_v hAc_v K hK0
  have hη := etaT_inv_le_of_plainN (band d) hE hv1 hc0 hAc_v
  have hA := scale_ge_one_of_hreg_plainN d hE hsv hv1 hc0 hreg0_v hAc_v
  have hKD := eventually_kDecayRegime d (m + 2) hτ'0 D'
  have hPY := ev_PYQN d m (C_P := C_P) (by rw [hC_P, hnRm]; push_cast; linarith) hE hv1 hη
  have hmN : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have ha1 := ev_ha1Q d m (ε := ε₀) (ε₁ := ε₁) hτ'0.le (by
    have : ((3 * m + 5 : ℕ) : ℝ) * τ' ≤ ε₀ / 16 := by
      push_cast
      have h : ((3 : ℝ) * m + 5) ≤ 3 * nR + 1 := by rw [hnRm]; linarith
      have := mul_le_mul_of_nonneg_right h hτ'0.le
      nlinarith
    rw [hε₁]; linarith)
  have ha2 := ev_ha2QN d m (ε := ε₀) (ε₁ := ε₁) (CK := CK) hτ'0.le hε₁0.le hCK0 hκ0 hEκ (by
    have : ((3 * m + 6 : ℕ) : ℝ) * τ' ≤ ε₀ / 16 := by
      push_cast
      have h : ((3 : ℝ) * m + 6) ≤ 3 * nR + 1 := by rw [hnRm]; linarith
      have := mul_le_mul_of_nonneg_right h hτ'0.le
      nlinarith
    rw [hε₁]; linarith)
  have ha3 := ev_ha3QN d m (ε := ε₀) (ε₁ := ε₁) hτ'0 hτ'1 hε₁0.le hκ0 hEκ (by
    have : ((6 * m + 11 : ℕ) : ℝ) * τ' ≤ 2 * ε₀ / 16 := by
      push_cast
      have h : ((6 : ℝ) * m + 11) ≤ 2 * (3 * nR + 1) := by rw [hnRm]; linarith
      have := mul_le_mul_of_nonneg_right h hτ'0.le
      nlinarith
    rw [hε₁]; linarith)
  have ha4 := ev_ha4Q d m (ε := ε₀) (ε₁ := ε₁) hτ'0.le (by
    have : ((m : ℕ) : ℝ) * τ' ≤ ε₀ / 16 := by
      have h : (m : ℝ) ≤ 3 * nR + 1 := by rw [hnRm]; linarith
      have := mul_le_mul_of_nonneg_right h hτ'0.le
      nlinarith
    rw [hε₁]; linarith)
  have hc2 := cTwo52_pos
  have hT1 := ev_tailW d (cKerSumZero (m + 2) * 16 ^ (2 * (m + 2)) * (2 * cTwo52) ^ (m + 1))
    (PT m) q hPTD' (R := 4096) (by norm_num)
  have hT2W := ev_tailW d (cKerSumZeroErr (m + 2) * (1 + (2 * cTwo52) ^ (m + 1))) (PT m) q hPTD'
    (R := 8192) (by norm_num)
  have hT2E := ev_tailExp d (3 * cKerSumZeroErr (m + 2) * (24 * Real.exp 1 * cTwo52) ^ (m + 1))
    (PT m) q cZero_pos hτ'0 (R := 8192) (by norm_num)
  have hT3W := ev_tailW d (C3W m) (PT m) q hPTD' (R := 8192) (by norm_num)
  have hT3E := ev_tailExp d (C3E m) (PT m) q cZero_pos hτ'0 (R := 8192) (by norm_num)
  have hT4W := ev_tailW d (C4W m) (PT m) q hPTD (R := 8192) (by norm_num)
  have hT4E := ev_tailExp d (C4E m) (PT m) q cZero_pos hτ'0 (R := 8192) (by norm_num)
  have hT5 := ev_ht5 m
  have hT6 := ev_ht6 m (C_K := C_K) (by
    rw [hC_K, hD', hD_Yv, hC_P, hnRm]; push_cast; nlinarith)
  have hT7 := ev_tailW d (cTwo52 ^ (m + 1)) (PT m) q hPTD' (R := 4096) (by norm_num)
  have hshX := ev_rpow_le (a := ((2 * (2 * (m + 2) + 2) : ℕ) : ℝ) - C_K) (b := 0)
    (by rw [hC_K, hD', hD_Yv, hC_P]; push_cast; nlinarith [hnRm]) ((2 * (m + 2) + 2 : ℕ) : ℝ)
  have hshD := ev_rpow_le (a := ((2 * (m + 2) + 2 + 1 : ℕ) : ℝ) - C_K) (b := -D')
    (by rw [hC_K, hD', hD_Yv, hC_P]; push_cast; nlinarith [hnRm]) ((2 * (m + 2) + 2 : ℕ) : ℝ)
  have hΔN := ev_rpow_le (a := 1 - C_K) (b := 0) (by rw [hC_K, hD', hD_Yv, hC_P]; nlinarith) 2
  have hLmK := hB.LmK (m + 2) (by omega) ε hε D hD
  have hGoodD := hGood (D + 1) (by linarith)
  filter_upwards [hLmK, hΛ1, hasmAll, hGoodD, hInit, eventually_ge_atTop 4, hlog,
    hη, ev_dims514 d, hA, hKD, hPY, ha1, ha2, ha3, ha4, hT1, hT2W, hT2E, hT3W, hT3E, hT4W, hT4E,
    hT5, hT6, hT7, hshX, hshD, hΔN, eventually_ge_atTop ⌈CK + 1⌉₊]
    with N hLmKN hΛN hasmN hGoodN hInitN hN4 hlogN hηN hdN hAN hKDN hPYN ha1N ha2N ha3N ha4N
      hT1N hT2WN hT2EN hT3WN hT3EN hT4WN hT4EN hT5N hT6N hT7N hshXN hshDN hΔNN hCKNN
  obtain ⟨hN1, hW2, hWN, hLN, hLWN, hcardN, hsqN⟩ := hdN
  have hN1n : 1 ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  have hNε : (N : ℝ) ^ ε₀ ≤ (N : ℝ) ^ ε := Real.rpow_le_rpow_of_exponent_le hN1 hε₀ε
  have hAv0 : 0 < (band d).scale (E N) N (v N) := (band d).scale_pos' (hE N) N ((hs0 N).trans (hsv N)) (hv1 N)
  set g : ℝ := (Λ N ^ ((1 : ℝ) / 2) + Φ N) * ((band d).scale (E N) N (v N) ^ (m + 2))⁻¹ with hg
  have hΛh : 1 ≤ Λ N ^ ((1 : ℝ) / 2) := Real.one_le_rpow hΛN (by norm_num)
  have hg0 : 0 ≤ g := by rw [hg]; have := hΦ0 N; positivity
  by_cases hsvN : s N = v N
  · -- the degenerate window `s N = v N`: directly (2.68) at `s`
    refine le_trans (measure_mono ?_) hLmKN
    intro ω hω
    obtain ⟨q', hq'⟩ := hω
    refine ⟨q', ?_⟩
    change (N : ℝ) ^ ε * g < (if q'.1 = sigmaAltGen (m + 2) ∨ q'.1 = sigmaAltGen' (m + 2) then
      ‖SumZeroDyn.lkT (sample d) (E N) N (v N) ω q'.1 q'.2‖ else 0) at hq'
    change (N : ℝ) ^ ε * ((band d).scale (E N) N (s N))⁻¹ ^ (m + 2) < (sample d).lkErr (E N) N (s N) ω q'.idx
    split_ifs at hq' with hna
    · have e1 : ‖SumZeroDyn.lkT (sample d) (E N) N (v N) ω q'.1 q'.2‖ = (sample d).lkErr (E N) N (s N) ω q'.idx := by
        rw [SumZeroDyn.norm_lkT, ← hsvN]
      rw [e1] at hq'
      have hle : ((band d).scale (E N) N (s N))⁻¹ ^ (m + 2) ≤ g := by
        rw [hg, hsvN, inv_pow]
        have h0 : 0 ≤ ((band d).scale (E N) N (v N) ^ (m + 2))⁻¹ := by positivity
        have : 1 ≤ Λ N ^ ((1 : ℝ) / 2) + Φ N := by linarith [hΦ0 N]
        nlinarith
      have := mul_le_mul_of_nonneg_left hle (Real.rpow_nonneg hN0.le ε)
      linarith
    · have : 0 ≤ (N : ℝ) ^ ε * g := mul_nonneg (Real.rpow_nonneg hN0.le _) hg0
      linarith
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
        + ((2 * (m + 2) + 2 : ℕ) : ℝ) * ((etaT (E N) (time s v K N (j + 1)))⁻¹ ^ (2 * (m + 2) + 2 + 1)
            * (time s v K N (j + 1) - time s v K N j))
          * ((band d).scale (E N) N (time s v K N j)) ^ (2 * (m + 2) + 2 - 1)
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
      have := shXi_le (N := N) (C_K := C_K) (2 * (m + 2) + 2) hN1 hx0 hx hA0 hA' hΔ0 hΔ hshXN he'
        (by omega)
      linarith
    have hshD' : ∀ j < K N, ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ 2 * (m + 2) + 2 →
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
    have hGex := fun σ : {σ : Fin (m + 2) → Bool // IsAltQ m σ} =>
      hasmN σ (Λ N) (Φ N) ((band d).ell N (s N)) (hΛ0 N) (hΦ0 N) (hs0 N) hlt (hv1 N) hKN1 hKle hΔ
        (by rw [Real.rpow_one]; exact hLN) hAN hKDN hPYN hshΞ hshD'
    choose G hGP hGb using hGex
    -- the flow bad set is a preimage under `H_v`
    set Sbad : Set (Matrix (d.Idx N) (d.Idx N) ℂ) := {M | ∃ q : LoopData (d.L N) (m + 2),
      (N : ℝ) ^ ε * g < (if q.1 = sigmaAltGen (m + 2) ∨ q.1 = sigmaAltGen' (m + 2) then
        ‖gloop (d.L N) (d.W N) M (zt (E N) (v N)) q.idx - (band d).Kval (E N) N (v N) q.idx‖ else 0)}
      with hSbad
    have hSm : MeasurableSet Sbad := by
      have : Sbad = ⋃ q : LoopData (d.L N) (m + 2), {M | (N : ℝ) ^ ε * g <
          (if q.1 = sigmaAltGen (m + 2) ∨ q.1 = sigmaAltGen' (m + 2) then
            ‖gloop (d.L N) (d.W N) M (zt (E N) (v N)) q.idx - (band d).Kval (E N) N (v N) q.idx‖ else 0)} := by
        ext M; simp [hSbad]
      rw [this]
      refine MeasurableSet.iUnion fun q => measurableSet_lt measurable_const ?_
      split_ifs
      · exact ((measurable_gloop_matrix d N _ _).sub measurable_const).norm
      · exact measurable_const
    set Good := {ω : Ωg d | ∀ k : Fin (K N + 1), H d s v K N k ω ∈ goodSet514 d (E N) N
      (time s v K N k) (m + 2) ε₁ (Λ N) (Φ N) τ' D' ((band d).ell N (s N))} with hGooddef
    set Init := {ω : Ωg d | ∀ q : LoopData (d.L N) (m + 2),
      ‖gloop (d.L N) (d.W N) (H d s v K N 0 ω) (zt (E N) (s N)) q.idx - (band d).Kval (E N) N (s N) q.idx‖
        ≤ (N : ℝ) ^ ε₁ * ((band d).scale (E N) N (s N))⁻¹ ^ (m + 2)} with hInitdef
    have hsub : H d s v K N (K N) ⁻¹' Sbad ⊆ Goodᶜ ∪ Initᶜ ∪ ⋃ σ, (G σ)ᶜ := by
      intro ω hω
      by_contra hno
      simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_iUnion, not_or, not_exists,
        not_not] at hno
      obtain ⟨⟨hgood, hinit⟩, hG⟩ := hno
      obtain ⟨q', hq'⟩ := hω
      have hna : IsAltQ m q'.1 := by
        by_contra h
        have h' : ¬ (q'.1 = sigmaAltGen (m + 2) ∨ q'.1 = sigmaAltGen' (m + 2)) := h
        simp only [h', ↓reduceIte] at hq'
        have : 0 ≤ (N : ℝ) ^ ε * g := mul_nonneg (Real.rpow_nonneg hN0.le _) hg0
        linarith
      have hna' : q'.1 = sigmaAltGen (m + 2) ∨ q'.1 = sigmaAltGen' (m + 2) := hna
      simp only [hna', ↓reduceIte] at hq'
      have hτK : goodExitTau514 d (E N) s v K (m + 2) ε₁ (Λ N) (Φ N) τ' D' ((band d).ell N (s N)) N ω
          = K N := goodExitTau514_eq_of_forall_mem d (E N) s v K (m + 2) ε₁ (Λ N) (Φ N) τ' D' _ N hgood
      have hb := hGb ⟨q'.1, hna⟩ ω (hG ⟨q'.1, hna⟩) (by rw [hτK]; omega) q'.2
      dsimp only at hb
      rw [hτK] at hb
      rw [AfrozQ_eq_of_eq d (hE N) (hs0 N) (hsv N) (hv1 N) q'.1 hτK] at hb
      -- the initial datum
      set X0 := Finset.univ.sup' Finset.univ_nonempty (fun b => ‖AtrueN d (E N) s v K N q'.1 0 ω b‖)
        with hX0def
      have hX0 : X0 ≤ (N : ℝ) ^ ε₁ * ((band d).scale (E N) N (s N))⁻¹ ^ (m + 2) := by
        refine Finset.sup'_le _ _ fun b _ => ?_
        have e : AtrueN d (E N) s v K N q'.1 0 ω b = gloop (d.L N) (d.W N) (H d s v K N 0 ω) (zt (E N) (s N))
            (LoopData.idx (q'.1, b)) - (band d).Kval (E N) N (s N) (LoopData.idx (q'.1, b)) := by
          unfold AtrueN LvalN KvN; rw [time_zero]; rfl
        rw [e]; exact hinit (q'.1, b)
      have hX00 : 0 ≤ X0 := by
        obtain ⟨b0⟩ := (inferInstance : Nonempty (LoopArg (d.L N) (m + 2)))
        exact (norm_nonneg _).trans (Finset.le_sup' (fun b => ‖AtrueN d (E N) s v K N q'.1 0 ω b‖)
          (Finset.mem_univ b0))
      have hgood0 := hgood ⟨0, by omega⟩
      have hS0 : Finset.univ.sup' Finset.univ_nonempty (fun b => ‖AtrueQ d (E N) s v K N q'.1 0 ω b‖)
          ≤ (1 + (6 * Real.exp 1 * cTwo52 * (4 * (d.W N : ℝ) ^ τ')) ^ (m + 1)) * X0
            + (2 * cTwo52) ^ (m + 1) * (d.L N : ℝ) ^ (m + 1) * (d.W N : ℝ) ^ (-D') := by
        refine Finset.sup'_le _ _ fun b _ => ?_
        exact norm_AtrueQ0_le d s v K N q'.1 ω hτ'0 ((hs0 N).trans (hmem 0 (Nat.zero_le _)).1)
          ((hmem 0 (Nat.zero_le _)).2.trans_lt (hv1 N)) hgood0 hX00
          (fun b' => Finset.le_sup' (fun b => ‖AtrueN d (E N) s v K N q'.1 0 ω b‖) (Finset.mem_univ b')) b
      -- the endpoint quantities at `K`
      have hgoodK := hgood ⟨K N, by omega⟩
      rw [time_last s v K N (hK0 N)] at hgoodK
      have hgoodK' := hgoodK
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨_, h2K⟩, _⟩, _⟩, _⟩, _⟩, hlkK⟩, _⟩, _⟩ := hgoodK'
      have hXi : xiLKB (band d) (E N) N (v N) (H d s v K N (K N) ω) (m + 1) ≤ (N : ℝ) ^ ε₁ * Φ N :=
        h2K (m + 1) (by omega) (by omega)
      have hQe := Qop_endpoint' d (hE N) (t := v N) ((hs0 N).trans (hsv N)) (hv1 N) hτ'0.le
        (n := m) (m₀ := 2 * (m + 2) + 2) (by omega) hna.nonconst
        (H_isHermitian d s v K N (K N) ω) hlkK q'.2
      have hAtrueN : AtrueN d (E N) s v K N q'.1 (K N) ω = lkTM (band d) (E N) N (v N) (H d s v K N (K N) ω) q'.1 := by
        unfold AtrueN; rw [time_last s v K N (hK0 N)]; rfl
      have hAtrueQ : AtrueQ d (E N) s v K N q'.1 (K N) ω
          = Qop (d.L N) ((v N : ℝ) : ℂ) (lkTM (band d) (E N) N (v N) (H d s v K N (K N) ω) q'.1) := by
        unfold AtrueQ; rw [hAtrueN, time_last s v K N (hK0 N)]
      have hCKN : CK + 1 ≤ (N : ℝ) := (Nat.le_ceil (CK + 1)).trans (by exact_mod_cast hCKNN)
      have hΔN' : step s v K N * (2 * (N : ℝ)) ≤ 1 := by
        have e : (N : ℝ) ^ (-C_K) * (2 * (N : ℝ)) = 2 * (N : ℝ) ^ (1 - C_K) := by
          rw [show 1 - C_K = -C_K + 1 by ring, Real.rpow_add hN0, Real.rpow_one]; ring
        have := mul_le_mul_of_nonneg_right hΔ (by positivity : (0 : ℝ) ≤ 2 * (N : ℝ))
        linarith
      have hwN : (d.W N : ℝ) ^ τ' ≤ N := by
        calc (d.W N : ℝ) ^ τ' ≤ (N : ℝ) ^ τ' := Real.rpow_le_rpow (by positivity) hWN hτ'0.le
          _ ≤ (N : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 hτ'1
          _ = N := Real.rpow_one _
      have hw1 : 1 ≤ (d.W N : ℝ) ^ τ' := Real.one_le_rpow (by exact_mod_cast d.W_pos N) hτ'0.le
      have hNε1 : (N : ℝ) ^ ε₁ ≤ N := by
        calc (N : ℝ) ^ ε₁ ≤ (N : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 hε₁1
          _ = N := Real.rpow_one _
      set Tn := ((N : ℝ) ^ q)⁻¹ / 4096 with hTn
      have hhalf : ((N : ℝ) ^ q)⁻¹ / 8192 + ((N : ℝ) ^ q)⁻¹ / 8192 = Tn := by rw [hTn]; ring
      -- the tails
      have ht1 := (tail1_le d N m (τ' := τ') (D' := D') hN1 hLN hwN (by linarith)).trans hT1N
      have ht2 := (tail2_le d N m (τ' := τ') (D' := D') hN1 hLN hwN hw1 hCK0 hCKN).trans
        (add_le_add hT2WN hT2EN)
      rw [hhalf] at ht2
      have ht3 := (tail3_le d N m (ε₁ := ε₁) (τ' := τ') (D' := D') (Φ := Φ N) hN1 hLN hLWN hwN hw1
        hNε1 (hΦ0 N) hCK0 hCKN).trans
        (mul_le_mul_of_nonneg_left (add_le_add hT3WN hT3EN) (by linarith [hΦ0 N]))
      rw [hhalf] at ht3
      have ht4 := (tail4_le d N m (ε₁ := ε₁) (τ' := τ') (D'' := D' - 1) hN1 hLN hWN hLWN hwN hw1
        hNε1 hΛN).trans
        (mul_le_mul_of_nonneg_left (add_le_add hT4WN hT4EN) (by linarith))
      rw [hhalf] at ht4
      have ht6 := hT6N (step s v K N) hΔ0 hΔ
      have ht7 := (tail7_le d N m (D' := D') hN1).trans hT7N
      have hbud := budgetQ d (m := m) (hE N) s v K N (ε := ε₀) (ε₁ := ε₁) (τ' := τ') (D' := D')
        (D_Y := D_Y) (Λ := Λ N) (Φ := Φ N) (CK := CK) (X0 := X0)
        (S0 := Finset.univ.sup' Finset.univ_nonempty (fun b => ‖AtrueQ d (E N) s v K N q'.1 0 ω b‖))
        (XiK := xiLKB (band d) (E N) N (v N) (H d s v K N (K N) ω) (m + 1)) q'.2
        (hs0 N) hlt (hv1 N) hKN1 hN1 hWN hLN hcardN hLWN hηN hAN hΛN (hΦ0 N) hCK0 hCKN hΔN'
        hτ'0.le hε₁0.le hε₁1 hε₀0.le hlogN hX00 hX0 hS0 hXi ha1N ha2N ha3N ha4N ht1 ht2 ht3 ht4
        (by rw [hD_Y]; exact hT5N) ht6 ht7
      -- combine
      have hAt : AtrueN d (E N) s v K N q'.1 (K N) ω q'.2
          = gloop (d.L N) (d.W N) (H d s v K N (K N) ω) (zt (E N) (v N)) q'.idx
            - (band d).Kval (E N) N (v N) q'.idx := by
        unfold AtrueN LvalN KvN; rw [time_last s v K N (hK0 N)]; rfl
      have htri : ‖AtrueN d (E N) s v K N q'.1 (K N) ω q'.2‖
          ≤ ‖AtrueQ d (E N) s v K N q'.1 (K N) ω q'.2‖
            + ‖lkTM (band d) (E N) N (v N) (H d s v K N (K N) ω) q'.1 q'.2
              - Qop (d.L N) ((v N : ℝ) : ℂ) (lkTM (band d) (E N) N (v N) (H d s v K N (K N) ω) q'.1) q'.2‖ := by
        rw [hAtrueQ, hAtrueN]
        have := norm_add_le (Qop (d.L N) ((v N : ℝ) : ℂ)
            (lkTM (band d) (E N) N (v N) (H d s v K N (K N) ω) q'.1) q'.2)
          (lkTM (band d) (E N) N (v N) (H d s v K N (K N) ω) q'.1 q'.2
            - Qop (d.L N) ((v N : ℝ) : ℂ) (lkTM (band d) (E N) N (v N) (H d s v K N (K N) ω) q'.1) q'.2)
        simp only [add_sub_cancel] at this
        exact this
      rw [hAt] at htri
      have hfin := htri.trans (add_le_add hb hQe)
      have hfin2 := hfin.trans hbud
      have hle : (N : ℝ) ^ ε₀ * (Λ N ^ ((1 : ℝ) / 2) + Φ N)
          * ((band d).scale (E N) N (v N) ^ (m + 2))⁻¹ ≤ (N : ℝ) ^ ε * g := by
        rw [hg, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hNε (by linarith [hΦ0 N]))
          (by positivity)
      linarith
    -- probability
    have hbadeq : badSet (fun N (q : LoopData ((band d).L N) (m + 2)) ω =>
          if q.1 = sigmaAltGen (m + 2) ∨ q.1 = sigmaAltGen' (m + 2)
          then ‖SumZeroDyn.lkT (sample d) (E N) N (v N) ω q.1 q.2‖ else 0)
        (fun N _ _ => (Λ N ^ ((1 : ℝ) / 2) + Φ N) * ((band d).scale (E N) N (v N) ^ (m + 2))⁻¹) ε N
        = Hflow d N (time s v K N (K N)) ⁻¹' Sbad := by
      rw [time_last s v K N (hK0 N)]
      ext ω
      rfl
    have hx0 : (0 : ℝ) ≤ (N : ℝ) ^ (-(D + 1)) := Real.rpow_nonneg hN0.le _
    have hGσ : ∀ σ, (Pg d) (G σ)ᶜ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))) := fun σ => by
      rw [← ofReal_measureReal]; exact ENNReal.ofReal_le_ofReal (hGP σ)
    have hcard2 : (Fintype.card {σ : Fin (m + 2) → Bool // IsAltQ m σ} : ℝ) ≤ 2 := by
      have hsub2 : Finset.univ.filter (IsAltQ m) ⊆ {sigmaAltGen (m + 2), sigmaAltGen' (m + 2)} := by
        intro σ hσ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
        rcases hσ with h | h <;> simp [h]
      have h1 : Fintype.card {σ : Fin (m + 2) → Bool // IsAltQ m σ}
          = (Finset.univ.filter (IsAltQ m)).card := Fintype.card_subtype _
      have h2 := Finset.card_le_card hsub2
      have h3 : ({sigmaAltGen (m + 2), sigmaAltGen' (m + 2)} : Finset (Fin (m + 2) → Bool)).card ≤ 2 :=
        Finset.card_le_two
      have : Fintype.card {σ : Fin (m + 2) → Bool // IsAltQ m σ} ≤ 2 := by omega
      exact_mod_cast this
    have hreal : (2 + (Fintype.card {σ : Fin (m + 2) → Bool // IsAltQ m σ} : ℝ))
        * (N : ℝ) ^ (-(D + 1)) ≤ (N : ℝ) ^ (-D) := by
      have hN4' : (4 : ℝ) ≤ N := by exact_mod_cast hN4
      have e : (N : ℝ) * (N : ℝ) ^ (-(D + 1)) = (N : ℝ) ^ (-D) := by
        rw [show -(D + 1) = -D + (-1) by ring, Real.rpow_add hN0, Real.rpow_neg_one]
        field_simp
      have : (2 + (Fintype.card {σ : Fin (m + 2) → Bool // IsAltQ m σ} : ℝ))
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
          + ∑ _σ : {σ : Fin (m + 2) → Bool // IsAltQ m σ},
              ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))) :=
          add_le_add (add_le_add hGoodN hInitN) (Finset.sum_le_sum fun σ _ => hGσ σ)
      _ = ENNReal.ofReal ((2 + (Fintype.card {σ : Fin (m + 2) → Bool // IsAltQ m σ} : ℝ))
            * (N : ℝ) ^ (-(D + 1))) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_add (by norm_num) (by positivity), ENNReal.ofReal_natCast,
            ENNReal.ofReal_ofNat]
          ring
      _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := ENNReal.ofReal_le_ofReal hreal

/-- **The endpoint bound for the alternating `σ` of length two**, under the plain pair, from
`endpoint_alt_all_plainN` at `m = 0`. -/
theorem endpoint_alt_two_hEndAlt_plainN {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) {E : ℕ → ℝ}
    (hEκ : ∀ N, |E N| ≤ 2 - κ) {s t : ℕ → ℝ} (hB : BoundsCoreN (sample d) E s)
    (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c)
    (hreg0 : ∀ᶠ N : ℕ in atTop, (etaT (E N) (s N) / etaT (E N) (t N)) ^ 30 ≤
      (band d).scale (E N) N (t N))
    (hAc : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale (E N) N (t N)) :
    ∀ Λ Φ : ℕ → ℝ, (∀ N, 0 ≤ Λ N) → (∀ N, 0 ≤ Φ N) →
      (∀ᶠ N : ℕ in atTop, 1 ≤ Λ N) → Lemma514PremisesN (sample d) E s t 2 Λ Φ →
      ∀ v : ℕ → ℝ, (∀ N, v N ∈ Set.Icc (s N) (t N)) →
        StochDom (band d).P
          (fun N (q : {q : LoopData ((band d).L N) 2 //
              q.1 = Grid.sigmaAltGen 2 ∨ q.1 = Grid.sigmaAltGen' 2}) ω =>
            ‖SumZeroDyn.lkT (sample d) (E N) N (v N) ω q.1.1 q.1.2‖)
          (fun N _ _ => (Λ N ^ ((1 : ℝ) / 2) + Φ N) * ((band d).scale (E N) N (v N) ^ 2)⁻¹) := by
  intro Λ Φ hΛ0 hΦ0 hΛ1 hprem v hv
  have h := endpoint_alt_all_plainN d hκ0 hκ1 hEκ hB hs0 ht1 hc0 hreg0 hAc 0 Λ Φ hΛ0 hΦ0 hΛ1 hprem
    v hv
  intro τ hτ D hD
  filter_upwards [h τ hτ D hD] with N hN
  refine le_trans (measure_mono ?_) hN
  intro ω hω
  obtain ⟨q, hq⟩ := hω
  refine ⟨q.1, ?_⟩
  have hc : q.1.1 = sigmaAltGen (0 + 2) ∨ q.1.1 = sigmaAltGen' (0 + 2) := q.2
  change (N : ℝ) ^ τ * ((Λ N ^ ((1 : ℝ) / 2) + Φ N) * ((band d).scale (E N) N (v N) ^ (0 + 2))⁻¹)
    < (if q.1.1 = sigmaAltGen (0 + 2) ∨ q.1.1 = sigmaAltGen' (0 + 2)
      then ‖SumZeroDyn.lkT (sample d) (E N) N (v N) ω q.1.1 q.1.2‖ else 0)
  rw [ite_cond_eq_true _ _ (eq_true hc)]
  exact hq

section CompatQ

end CompatQ

end RBM.Gauss.Grid
