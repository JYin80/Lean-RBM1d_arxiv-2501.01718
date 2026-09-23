/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingDriftAtProfile
import RBM1D.Gauss.APrimeQVGlobalPoly

/-!
# T611: all-sample general-moving drift envelope

This file gives the deterministic polynomial envelope needed to split the
general-moving drift moment over the common event and its complement.  The
bound is uniform in the active target-mesh cell, including `k = 0`, in the
closed running-time interval, in the output coordinate, and in the sample.
-/

namespace RBM.APrimeGeneralMovingDriftGlobalPoly

open Filter Gauss CutHypTheta
open scoped Matrix.Norms.L2Operator

private noncomputable abbrev d : Gauss.Dims := Gauss.Dims.exampleGrow
private noncomputable abbrev B : Band (Gauss.Ω d) := Gauss.band d

/-- With `eta_v^{-1} <= N`, the unpropagated two-loop drift costs at most
seven powers of `N`.  The coefficient depends only on the fixed `Kval`
window constant. -/
private theorem norm_driftF_le_constant_mul_pow_seven
    {E : ℝ} (hE : |E| < 2) {CK : ℝ} (hCK0 : 0 ≤ CK)
    (hCK : ∀ (N : ℕ) (u v : ℝ), 0 ≤ u → u ≤ v → v < 1 →
      ∀ J : LoopIdx (ZMod (B.L N)), J.WF → 2 ≤ J.length → J.length ≤ 2 →
        ‖B.Kval E N u J‖ ≤ CK * (etaT E v)⁻¹ ^ 2)
    (N : ℕ) (hN : 1 ≤ (N : ℝ))
    (hWL : (B.W N : ℝ) * (B.L N : ℝ) ≤ (N : ℝ))
    {u v : ℝ} (hu0 : 0 ≤ u) (huv : u ≤ v) (hv1 : v < 1)
    (hη : (N : ℝ) ^ (-(1 : ℝ)) ≤ etaT E v)
    (ω : Gauss.Ω d) (σ : Fin 2 → Bool) (a : LoopArg (d.L N) 2) :
    ‖DriftDef.driftF B E N u ((Gauss.sample d).H N u ω) σ a‖ ≤
      (52 * (1 + CK) ^ 2) * (N : ℝ) ^ (7 : ℕ) := by
  have hNpos : 0 < (N : ℝ) := by linarith
  have hηpos : 0 < etaT E v := Step2.etaT_pos' hE hv1
  have hηinv : (etaT E v)⁻¹ ≤ (N : ℝ) := by
    have hi := inv_anti₀ (Real.rpow_pos_of_pos hNpos (-(1 : ℝ))) hη
    simpa only [Real.rpow_neg hNpos.le, Real.rpow_one, inv_inv] using hi
  let M : ℝ := (1 + CK) * (N : ℝ) ^ (3 : ℕ)
  have hM0 : 0 ≤ M := by
    dsimp [M]
    positivity
  have hM1 : 1 ≤ M := by
    have hN3 : (1 : ℝ) ≤ (N : ℝ) ^ (3 : ℕ) := one_le_pow₀ hN
    dsimp [M]
    nlinarith [mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ 1 + CK by linarith)
      (show 0 ≤ (N : ℝ) ^ (3 : ℕ) by positivity)]
  have hG : ∀ J : LoopIdx (ZMod (B.L N)), J.WF →
      1 ≤ J.length → J.length ≤ 3 →
      ‖gloop (B.L N) (B.W N) ((Gauss.sample d).H N u ω) (zt E u) J‖ ≤ M := by
    intro J hJ hJ1 hJ3
    have hh := Gauss.norm_gloop_le_win
      (Gauss.Hflow_isHermitian d N u ω) hE hu0 huv hv1 3 J hJ hJ1 hJ3
    have hp : (etaT E v)⁻¹ ^ (3 : ℕ) ≤ (N : ℝ) ^ (3 : ℕ) :=
      pow_le_pow_left₀ (inv_nonneg.mpr hηpos.le) hηinv 3
    calc
      _ ≤ (etaT E v)⁻¹ ^ (3 : ℕ) := hh
      _ ≤ (N : ℝ) ^ (3 : ℕ) := hp
      _ ≤ (1 + CK) * (N : ℝ) ^ (3 : ℕ) := by
        exact le_mul_of_one_le_left (by positivity) (by linarith)
      _ = M := rfl
  have hK : ∀ J : LoopIdx (ZMod (B.L N)), J.WF →
      2 ≤ J.length → J.length ≤ 2 → ‖B.Kval E N u J‖ ≤ M := by
    intro J hJ hJ2 hJle
    have hh := hCK N u v hu0 huv hv1 J hJ hJ2 hJle
    have hp : (etaT E v)⁻¹ ^ (2 : ℕ) ≤ (N : ℝ) ^ (2 : ℕ) :=
      pow_le_pow_left₀ (inv_nonneg.mpr hηpos.le) hηinv 2
    have hN23 : (N : ℝ) ^ (2 : ℕ) ≤ (N : ℝ) ^ (3 : ℕ) := by
      nlinarith [sq_nonneg ((N : ℝ) ^ (2 : ℕ))]
    calc
      _ ≤ CK * (etaT E v)⁻¹ ^ (2 : ℕ) := hh
      _ ≤ CK * (N : ℝ) ^ (2 : ℕ) := mul_le_mul_of_nonneg_left hp hCK0
      _ ≤ CK * (N : ℝ) ^ (3 : ℕ) := mul_le_mul_of_nonneg_left hN23 hCK0
      _ ≤ (1 + CK) * (N : ℝ) ^ (3 : ℕ) := by
        exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = M := rfl
  have hraw := Gauss.norm_driftF_le_crude B E N hE u
    ((Gauss.sample d).H N u ω) (n := 0) σ a (MG := M) (MK := M)
    hM0 hM0 hG hK
  have hbracket :
      2 * ((M + 1) * M) + 32 * M ^ 2 + 16 * M ^ 2 ≤ 52 * M ^ 2 := by
    nlinarith [sq_nonneg M]
  calc
    _ ≤ (B.W N : ℝ) * (((0 : ℝ) + 2)) *
          ((B.L N : ℝ) * ((M + 1) * M)) +
        (((0 : ℝ) + 2)) *
          (2 * ((B.W N : ℝ) * (((0 : ℝ) + 2)) ^ 2 *
            ((B.L N : ℝ) * (M * (M + M))))) +
        (B.W N : ℝ) * (((0 : ℝ) + 2)) ^ 2 *
          ((B.L N : ℝ) * ((M + M) * (M + M))) := by
      simpa using hraw
    _ = ((B.W N : ℝ) * (B.L N : ℝ)) *
          (2 * ((M + 1) * M) + 32 * M ^ 2 + 16 * M ^ 2) := by ring
    _ ≤ ((B.W N : ℝ) * (B.L N : ℝ)) * (52 * M ^ 2) :=
      mul_le_mul_of_nonneg_left hbracket (by positivity)
    _ ≤ (N : ℝ) * (52 * M ^ 2) :=
      mul_le_mul_of_nonneg_right hWL (by positivity)
    _ = (52 * (1 + CK) ^ 2) * (N : ℝ) ^ (7 : ℕ) := by
      dsimp [M]
      ring

/-- Before the last fixed-constant absorption, the normalized propagated
drift has exponent `D + 7`. -/
private theorem driftAt_le_constant_mul_rpow
    {E D : ℝ} (hE : |E| < 2) (hD : 0 ≤ D)
    {CK : ℝ} (hCK0 : 0 ≤ CK)
    (hCK : ∀ (N : ℕ) (u v : ℝ), 0 ≤ u → u ≤ v → v < 1 →
      ∀ J : LoopIdx (ZMod (B.L N)), J.WF → 2 ≤ J.length → J.length ≤ 2 →
        ‖B.Kval E N u J‖ ≤ CK * (etaT E v)⁻¹ ^ 2)
    (N : ℕ) (hN : 1 ≤ (N : ℝ))
    (hWL : (B.W N : ℝ) * (B.L N : ℝ) ≤ (N : ℝ))
    (hWN : (d.W N : ℝ) ≤ (N : ℝ))
    {s u v : ℝ} (hs0 : 0 ≤ s) (hsu : s ≤ u) (huv : u ≤ v)
    (hv1 : v < 1) (hη : (N : ℝ) ^ (-(1 : ℝ)) ≤ etaT E v)
    (ω : Gauss.Ω d) (σ : Fin 2 → Bool) (a : LoopArg (d.L N) 2) :
    APrimeDriftTimeFamily.driftAt d E D N σ a s v u ω ≤
      (52 * (1 + CK) ^ 2) * (N : ℝ) ^ (D + 7) := by
  have hNpos : 0 < (N : ℝ) := by linarith
  have hu0 : 0 ≤ u := hs0.trans hsu
  have hraw : ∀ b : LoopArg (d.L N) 2,
      ‖DriftDef.driftF B E N u ((Gauss.sample d).H N u ω) σ b‖ ≤
        (52 * (1 + CK) ^ 2) * (N : ℝ) ^ (7 : ℕ) :=
    fun b => norm_driftF_le_constant_mul_pow_seven hE hCK0 hCK N hN hWL
      hu0 huv hv1 hη ω σ b
  have hU := Gauss.norm_Uker_apply_le_ukerRow
    (xiOf (mSigma E) σ) (v : ℂ) u
    (DriftDef.driftF B E N u ((Gauss.sample d).H N u ω) σ) a hraw
  have hscale := APrimeQVGlobalPoly.inv_driftScale_mul_ukerRow_le d
    hE hD hs0 hsu huv hv1 N hWN σ a
  have hspos : 0 < APrimeDriftTimeFamily.driftScale d E D N a s v :=
    APrimeDriftTimeFamily.driftScale_pos d hE (hsu.trans huv) hv1 N a
  have hC0 : 0 ≤ (52 * (1 + CK) ^ 2) * (N : ℝ) ^ (7 : ℕ) := by positivity
  calc
    APrimeDriftTimeFamily.driftAt d E D N σ a s v u ω =
        (APrimeDriftTimeFamily.driftScale d E D N a s v)⁻¹ *
          ‖Uker (d.L N) (xiOf (mSigma E) σ) (u : ℂ) (v : ℂ)
            (DriftDef.driftF B E N u ((Gauss.sample d).H N u ω) σ) a‖ := by
      unfold APrimeDriftTimeFamily.driftAt
      rw [div_eq_inv_mul]
    _ ≤ (APrimeDriftTimeFamily.driftScale d E D N a s v)⁻¹ *
          (Gauss.ukerRow (xiOf (mSigma E) σ) (v : ℂ) a u *
            ((52 * (1 + CK) ^ 2) * (N : ℝ) ^ (7 : ℕ))) :=
      mul_le_mul_of_nonneg_left hU (inv_nonneg.mpr hspos.le)
    _ = ((APrimeDriftTimeFamily.driftScale d E D N a s v)⁻¹ *
          Gauss.ukerRow (xiOf (mSigma E) σ) (v : ℂ) a u) *
            ((52 * (1 + CK) ^ 2) * (N : ℝ) ^ (7 : ℕ)) := by ring
    _ ≤ (N : ℝ) ^ D *
          ((52 * (1 + CK) ^ 2) * (N : ℝ) ^ (7 : ℕ)) :=
      mul_le_mul_of_nonneg_right hscale hC0
    _ = (52 * (1 + CK) ^ 2) * (N : ℝ) ^ (D + 7) := by
      rw [show (N : ℝ) ^ (7 : ℕ) = (N : ℝ) ^ (7 : ℝ) by
        norm_num [Real.rpow_natCast]]
      calc
        (N : ℝ) ^ D * (52 * (1 + CK) ^ 2 * (N : ℝ) ^ (7 : ℝ)) =
            (52 * (1 + CK) ^ 2) *
              ((N : ℝ) ^ D * (N : ℝ) ^ (7 : ℝ)) := by ring
        _ = (52 * (1 + CK) ^ 2) * (N : ℝ) ^ (D + 7) := by
          rw [Real.rpow_add hNpos]

/-- All-sample polynomial envelope for the literal general-moving drift.
There is no event, support, cutoff, or moment-order hypothesis, and the
active-cell quantifier includes `k = 0`. -/
theorem eventually_abs_driftAt_le_rpow
    {E D c : Real} {s t : Nat -> Real}
    (hE : |E| < 2) (hD : 60 <= D)
    (hs0 : forall N, 0 <= s N)
    (hst : forall N, s N <= t N)
    (ht1 : forall N, t N < 1)
    (hc : 0 < c)
    (hreg : Cond272Reg B E s t c) :
    ∀ᶠ N : Nat in Filter.atTop, forall k : Nat,
      k <= cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N ->
      let v := cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k
      forall u, u ∈ Set.Icc (s N) v ->
      forall a : LoopArg (d.L N) 2, forall omega : Gauss.Ω d,
        |APrimeDriftTimeFamily.driftAt
            d E D N Step2.sigPM a (s N) v u omega|
          <= (N : Real) ^ (D + 8) := by
  obtain ⟨CK, hCK0, hCK⟩ := Gauss.exists_norm_Kval_le_win B hE 2
  let C : ℝ := 52 * (1 + CK) ^ 2
  have heta := Gauss.rpow_neg_one_le_etaT_of_scale_ge d hE ht1 hc hreg.2
  filter_upwards [heta, d.dim, eventually_ge_atTop 1,
    eventually_le_rpow C (by norm_num : (0 : ℝ) < 1)] with
      N hetaN hdim hNnat hCN
  have hN : 1 ≤ (N : ℝ) := by exact_mod_cast hNnat
  have hNpos : 0 < (N : ℝ) := by linarith
  have hCN' : C ≤ (N : ℝ) := by simpa only [Real.rpow_one] using hCN
  have hWL : (B.W N : ℝ) * (B.L N : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hdim.1
  have hL1 : 1 ≤ (d.L N : ℝ) := by
    exact_mod_cast (show 1 ≤ d.L N by have := d.three_le_L N; omega)
  have hW0 : 0 ≤ (d.W N : ℝ) := by positivity
  have hWN : (d.W N : ℝ) ≤ (N : ℝ) := by
    calc
      (d.W N : ℝ) = (d.W N : ℝ) * 1 := (mul_one _).symm
      _ ≤ (d.W N : ℝ) * (d.L N : ℝ) :=
        mul_le_mul_of_nonneg_left hL1 hW0
      _ ≤ (N : ℝ) := hWL
  intro k hk
  let v := cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k
  change ∀ u, u ∈ Set.Icc (s N) v →
    ∀ a : LoopArg (d.L N) 2, ∀ omega : Gauss.Ω d,
      |APrimeDriftTimeFamily.driftAt
          d E D N Step2.sigPM a (s N) v u omega| ≤
        (N : ℝ) ^ (D + 8)
  have hv : v ∈ Set.Icc (s N) (t N) :=
    MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) v
      (cutNetPt_mem_netFinset hk)
  have hv1 : v < 1 := hv.2.trans_lt (ht1 N)
  have hηv : (N : ℝ) ^ (-(1 : ℝ)) ≤ etaT E v :=
    hetaN.trans (Gauss.etaT_le_of_le hE hv.2)
  intro u hu a omega
  have hpoint := driftAt_le_constant_mul_rpow hE (show 0 ≤ D by linarith) hCK0 hCK
    N hN hWL hWN (hs0 N) hu.1 hu.2 hv1 hηv omega Step2.sigPM a
  have hspos : 0 < APrimeDriftTimeFamily.driftScale d E D N a (s N) v :=
    APrimeDriftTimeFamily.driftScale_pos d hE hv.1 hv1 N a
  have hdrift0 : 0 ≤ APrimeDriftTimeFamily.driftAt
      d E D N Step2.sigPM a (s N) v u omega := by
    unfold APrimeDriftTimeFamily.driftAt
    exact div_nonneg (norm_nonneg _) hspos.le
  rw [abs_of_nonneg hdrift0]
  calc
    APrimeDriftTimeFamily.driftAt d E D N Step2.sigPM a (s N) v u omega
        ≤ C * (N : ℝ) ^ (D + 7) := by simpa only [C] using hpoint
    _ ≤ (N : ℝ) * (N : ℝ) ^ (D + 7) :=
      mul_le_mul_of_nonneg_right hCN' (Real.rpow_nonneg hNpos.le _)
    _ = (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (D + 7) := by rw [Real.rpow_one]
    _ = (N : ℝ) ^ ((1 : ℝ) + (D + 7)) := (Real.rpow_add hNpos _ _).symm
    _ = (N : ℝ) ^ (D + 8) := by ring_nf

/-- The assumptions of the global envelope admit a positive-length moving
window.  No stochastic condition occurs in the witness statement. -/
theorem drift_envelope_hypotheses_witness :
    ∃ E D c : ℝ, ∃ s t : ℕ → ℝ,
      E = 0 ∧ D = 60 ∧ |E| < 2 ∧ 60 ≤ D ∧
      (∀ N, 0 ≤ s N) ∧ (∀ N, s N ≤ t N) ∧
      (∀ N, t N < 1) ∧ 0 < c ∧ Cond272Reg B E s t c ∧
      ∀ᶠ N : ℕ in Filter.atTop, s N < t N := by
  obtain ⟨tauPrime, _htauPrime, c, hc, s, t, _hsEq, hs0, hst, ht1,
    hreg, _hB, _hstep, hall⟩ :=
    APrimeGeneralMovingDriftAtProfile.positive_cell_full_drift_hypotheses_witness
  have hpos := hall 1 1 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨0, 60, c, s, t, rfl, rfl, by norm_num, by norm_num,
    hs0, hst, ht1, hc, hreg, ?_⟩
  filter_upwards [hpos] with N hN
  exact hN.1

end RBM.APrimeGeneralMovingDriftGlobalPoly

#print axioms RBM.APrimeGeneralMovingDriftGlobalPoly.eventually_abs_driftAt_le_rpow
#print axioms RBM.APrimeGeneralMovingDriftGlobalPoly.drift_envelope_hypotheses_witness
