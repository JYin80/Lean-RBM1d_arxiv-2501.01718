/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingCrossHcrossPositive
import RBM1D.Gauss.APrimeGeneralMovingCrossBudgetNormBadAllOrders
import RBM1D.Gauss.APrimeGeneralMovingJointRateMomentEventSplit

/-!
# T1201: norm-good reduction of the general-moving cross budget

For each fixed positive integer order, the literal T1089 cross budget is at
most its exact norm-good-restricted part plus T1195's all-order norm-bad
payment.  This is a decomposition and reduction only; the norm-good term is
left unevaluated.
-/

namespace RBM.APrimeGeneralMovingCrossBudgetGoodReduction

open Filter MeasureTheory Set Gauss CutHypTheta
open RBM.MomentDuhamel
open scoped Matrix.Norms.L2Operator

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev mesh (D : ℝ) : ℕ → ℝ :=
  APrimeGeneralMovingMesh.targetMesh D

/-- The literal T1089 joint rate restricted to the T1197/T1173 norm-good
event, with all consumer endpoints and charges retained. -/
noncomputable def normGoodJointRate (E D deltaWeight : ℝ) (s t : ℕ → ℝ)
    (N k : ℕ) (a : LoopArg (d.L N) 2) (r : ℝ) : Gauss.Ω d → ℝ :=
  (APrimeGeneralMovingGoodMesh.good N).indicator
    (fun ω => APrimeCrossJointSplit.jointRate d E D deltaWeight s (mesh D) N k
      (APrimeSmoothWeightActual.canonicalM d s t (mesh D) N)
      Step2.sigPM a (cutNetPt s (mesh D) N k) r ω)

/-- T1089's exact coefficient applied to the `2p` moment norm of the
norm-good-restricted literal joint rate. -/
noncomputable def normGoodCrossBudget (E D deltaWeight : ℝ)
    (s t : ℕ → ℝ) (N k p : ℕ) (a : LoopArg (d.L N) 2) (r : ℝ) : ℝ :=
  APrimeGeneralMovingCrossHcrossPositive.crossMomentCoeff p /
    (4 * (p : ℝ) * √r) *
      MomentDuhamel.momNorm (Gauss.P d) (2 * p)
        (normGoodJointRate E D deltaWeight s t N k a r)

/-- For every fixed `p ≥ 1`, one eventual cutoff works uniformly over the
active target-mesh cells, outputs, and positive running times in their closed
cells. The full T1089 cross budget is bounded by its exact norm-good-restricted
counterpart plus the `(15p/8) N⁻¹/√r` norm-bad payment. -/
theorem eventually_positiveTimeCrossBudget_le_normGood_add_normBad
    {E D c : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg (Gauss.band d) E s t c)
    {deltaWeight : ℝ} (hdeltaWeight : 0 ≤ deltaWeight)
    (p : ℕ) (hp : 1 ≤ p) :
    ∀ᶠ N : ℕ in atTop,
      ∀ k ≤ cutNetTop s t (mesh D) N,
      ∀ a : LoopArg (d.L N) 2,
      ∀ r ∈ Icc (s N) (cutNetPt s (mesh D) N k),
        0 < r →
          APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
              E D deltaWeight s t N k p a r ≤
            normGoodCrossBudget E D deltaWeight s t N k p a r +
              (15 * (p : ℝ) / 8) * (N : ℝ) ^ (-(1 : ℝ)) / √r := by
  have hsplit :=
    APrimeGeneralMovingJointRateMomentEventSplit.eventually_jointRate_pow_integral_eq_normGood_add_normBad
      hE hD hs0 hst ht1 hc hreg hdeltaWeight p hp
  have hbad :=
    APrimeGeneralMovingCrossBudgetNormBadAllOrders.eventually_normBad_crossBudget_allOrders_le
      hE hD hs0 hst ht1 hc hreg hdeltaWeight p hp
  filter_upwards [hsplit, hbad, eventually_ge_atTop 1]
    with N hsplitN hbadN hN
  intro k hk a r hr hr0
  let Ξ : Set (Gauss.Ω d) :=
    APrimeGeneralMovingGoodMesh.good N
  let Z : Gauss.Ω d → ℝ := fun ω =>
    APrimeCrossJointSplit.jointRate d E D deltaWeight s (mesh D) N k
      (APrimeSmoothWeightActual.canonicalM d s t (mesh D) N)
      Step2.sigPM a (cutNetPt s (mesh D) N k) r ω
  let Zgood : Gauss.Ω d → ℝ := Ξ.indicator Z
  let Zbad : Gauss.Ω d → ℝ := Ξᶜ.indicator Z
  have hq : 2 * p ≠ 0 := by omega
  have hNpos : 0 < N := by omega
  have hGoodMeas : MeasurableSet Ξ := by
    simpa [Ξ] using APrimeGeneralMovingGoodMesh.measurableSet_good N
  have hBadMeas : MeasurableSet Ξᶜ := hGoodMeas.compl
  have hsplitInt :
      (∫ ω, |Z ω| ^ (2 * p) ∂(Gauss.P d)) =
        (∫ ω in Ξ, |Z ω| ^ (2 * p) ∂(Gauss.P d)) +
          ∫ ω in Ξᶜ, |Z ω| ^ (2 * p) ∂(Gauss.P d) := by
    have hs := hsplitN k hk a r hr
    simpa [Ξ, Z, mesh,
      APrimeGeneralMovingJointRateMomentEventSplit.normGood,
      APrimeGeneralMovingJointRateNormBadPayment.normGood,
      APrimeGeneralMovingGoodMesh.good] using hs
  have hGoodMomentInt :
      (∫ ω, |Zgood ω| ^ (2 * p) ∂(Gauss.P d)) =
        ∫ ω in Ξ, |Z ω| ^ (2 * p) ∂(Gauss.P d) := by
    rw [← integral_indicator hGoodMeas]
    apply integral_congr_ae
    filter_upwards [] with ω
    by_cases hω : ω ∈ Ξ
    · simp [Zgood, hω]
    · simp [Zgood, hω, hq]
  have hBadMomentInt :
      (∫ ω, |Zbad ω| ^ (2 * p) ∂(Gauss.P d)) =
        ∫ ω in Ξᶜ, |Z ω| ^ (2 * p) ∂(Gauss.P d) := by
    rw [← integral_indicator hBadMeas]
    apply integral_congr_ae
    filter_upwards [] with ω
    by_cases hω : ω ∈ Ξᶜ
    · simp [Zbad, hω]
    · simp [Zbad, hω, hq]
  have hsumPow :
      MomentDuhamel.momNorm (Gauss.P d) (2 * p) Z ^ (2 * p) =
        MomentDuhamel.momNorm (Gauss.P d) (2 * p) Zgood ^ (2 * p) +
          MomentDuhamel.momNorm (Gauss.P d) (2 * p) Zbad ^ (2 * p) := by
    calc
      MomentDuhamel.momNorm (Gauss.P d) (2 * p) Z ^ (2 * p) =
          ∫ ω, |Z ω| ^ (2 * p) ∂(Gauss.P d) :=
        MomentDuhamel.momNorm_pow (Gauss.P d) hq Z
      _ = (∫ ω in Ξ, |Z ω| ^ (2 * p) ∂(Gauss.P d)) +
            ∫ ω in Ξᶜ, |Z ω| ^ (2 * p) ∂(Gauss.P d) := hsplitInt
      _ = (∫ ω, |Zgood ω| ^ (2 * p) ∂(Gauss.P d)) +
            ∫ ω, |Zbad ω| ^ (2 * p) ∂(Gauss.P d) := by
        rw [hGoodMomentInt, hBadMomentInt]
      _ = _ := by
        rw [← MomentDuhamel.momNorm_pow (Gauss.P d) hq Zgood,
          ← MomentDuhamel.momNorm_pow (Gauss.P d) hq Zbad]
  have hα0 : (0 : ℝ) ≤ (1 : ℝ) / ((2 * p : ℕ) : ℝ) := by positivity
  have hpR : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hα1 : (1 : ℝ) / ((2 * p : ℕ) : ℝ) ≤ 1 := by
    have hden : (1 : ℝ) ≤ ((2 * p : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ 2 * p by omega)
    rw [div_le_one (by positivity)]
    exact hden
  have hfullRoot :
      (MomentDuhamel.momNorm (Gauss.P d) (2 * p) Z ^ (2 * p)) ^
          ((1 : ℝ) / ((2 * p : ℕ) : ℝ)) =
        MomentDuhamel.momNorm (Gauss.P d) (2 * p) Z := by
    rw [one_div]
    exact Real.pow_rpow_inv_natCast
      (MomentDuhamel.momNorm_nonneg (Gauss.P d) (2 * p) Z) hq
  have hgoodRoot :
      (MomentDuhamel.momNorm (Gauss.P d) (2 * p) Zgood ^ (2 * p)) ^
          ((1 : ℝ) / ((2 * p : ℕ) : ℝ)) =
        MomentDuhamel.momNorm (Gauss.P d) (2 * p) Zgood := by
    rw [one_div]
    exact Real.pow_rpow_inv_natCast
      (MomentDuhamel.momNorm_nonneg (Gauss.P d) (2 * p) Zgood) hq
  have hbadRoot :
      (MomentDuhamel.momNorm (Gauss.P d) (2 * p) Zbad ^ (2 * p)) ^
          ((1 : ℝ) / ((2 * p : ℕ) : ℝ)) =
        MomentDuhamel.momNorm (Gauss.P d) (2 * p) Zbad := by
    rw [one_div]
    exact Real.pow_rpow_inv_natCast
      (MomentDuhamel.momNorm_nonneg (Gauss.P d) (2 * p) Zbad) hq
  have htriangle :
      MomentDuhamel.momNorm (Gauss.P d) (2 * p) Z ≤
        MomentDuhamel.momNorm (Gauss.P d) (2 * p) Zgood +
          MomentDuhamel.momNorm (Gauss.P d) (2 * p) Zbad := by
    calc
          MomentDuhamel.momNorm (Gauss.P d) (2 * p) Z =
          (MomentDuhamel.momNorm (Gauss.P d) (2 * p) Z ^ (2 * p)) ^
            ((1 : ℝ) / ((2 * p : ℕ) : ℝ)) := hfullRoot.symm
      _ =
          ((MomentDuhamel.momNorm (Gauss.P d) (2 * p) Zgood ^ (2 * p)) +
            MomentDuhamel.momNorm (Gauss.P d) (2 * p) Zbad ^ (2 * p)) ^
              ((1 : ℝ) / ((2 * p : ℕ) : ℝ)) := by rw [hsumPow]
      _ ≤
          (MomentDuhamel.momNorm (Gauss.P d) (2 * p) Zgood ^ (2 * p)) ^
              ((1 : ℝ) / ((2 * p : ℕ) : ℝ)) +
            (MomentDuhamel.momNorm (Gauss.P d) (2 * p) Zbad ^ (2 * p)) ^
              ((1 : ℝ) / ((2 * p : ℕ) : ℝ)) :=
        Real.rpow_add_le_add_rpow
          (pow_nonneg (MomentDuhamel.momNorm_nonneg (Gauss.P d) (2 * p) Zgood) _)
          (pow_nonneg (MomentDuhamel.momNorm_nonneg (Gauss.P d) (2 * p) Zbad) _)
          hα0 hα1
      _ = _ := by rw [hgoodRoot, hbadRoot]
  have hcoeff :
      0 ≤ APrimeGeneralMovingCrossHcrossPositive.crossMomentCoeff p /
        (4 * (p : ℝ) * √r) := by
    unfold APrimeGeneralMovingCrossHcrossPositive.crossMomentCoeff
    have hpRpos : 0 < (p : ℝ) := lt_of_lt_of_le (by norm_num) hpR
    positivity
  have htri :
      (APrimeGeneralMovingCrossHcrossPositive.crossMomentCoeff p /
        (4 * (p : ℝ) * √r)) *
          MomentDuhamel.momNorm (Gauss.P d) (2 * p) Z ≤
        (APrimeGeneralMovingCrossHcrossPositive.crossMomentCoeff p /
          (4 * (p : ℝ) * √r)) *
            MomentDuhamel.momNorm (Gauss.P d) (2 * p) Zgood +
          (APrimeGeneralMovingCrossHcrossPositive.crossMomentCoeff p /
            (4 * (p : ℝ) * √r)) *
              MomentDuhamel.momNorm (Gauss.P d) (2 * p) Zbad := by
    calc
      _ ≤ (APrimeGeneralMovingCrossHcrossPositive.crossMomentCoeff p /
          (4 * (p : ℝ) * √r)) *
            (MomentDuhamel.momNorm (Gauss.P d) (2 * p) Zgood +
              MomentDuhamel.momNorm (Gauss.P d) (2 * p) Zbad) :=
        mul_le_mul_of_nonneg_left htriangle hcoeff
      _ = _ := by ring
  have hbadBudget :
      (APrimeGeneralMovingCrossHcrossPositive.crossMomentCoeff p /
        (4 * (p : ℝ) * √r)) *
          MomentDuhamel.momNorm (Gauss.P d) (2 * p) Zbad ≤
        (15 * (p : ℝ) / 8) * (N : ℝ) ^ (-(1 : ℝ)) / √r := by
    have hb := hbadN k hk a r hr hr0
    simpa [APrimeGeneralMovingCrossBudgetNormBadAllOrders.normBadCrossBudgetAllOrders,
      APrimeGeneralMovingCrossBudgetNormBad.normBadJointRate,
      APrimeGeneralMovingGoodMesh.good,
      APrimeGeneralMovingJointRateMomentEventSplit.normGood,
      APrimeGeneralMovingJointRateNormBadPayment.normGood,
      Zbad, Z, Ξ, mesh] using hb
  calc
    APrimeGeneralMovingCrossHcrossPositive.positiveTimeCrossBudget
        E D deltaWeight s t N k p a r =
      (APrimeGeneralMovingCrossHcrossPositive.crossMomentCoeff p /
        (4 * (p : ℝ) * √r)) *
          MomentDuhamel.momNorm (Gauss.P d) (2 * p) Z := by
        rfl
    _ ≤
      (APrimeGeneralMovingCrossHcrossPositive.crossMomentCoeff p /
        (4 * (p : ℝ) * √r)) *
          MomentDuhamel.momNorm (Gauss.P d) (2 * p) Zgood +
        (APrimeGeneralMovingCrossHcrossPositive.crossMomentCoeff p /
          (4 * (p : ℝ) * √r)) *
            MomentDuhamel.momNorm (Gauss.P d) (2 * p) Zbad := htri
    _ ≤ normGoodCrossBudget E D deltaWeight s t N k p a r +
          (15 * (p : ℝ) / 8) * (N : ℝ) ^ (-(1 : ℝ)) / √r := by
        have hrewrite :
            (APrimeGeneralMovingCrossHcrossPositive.crossMomentCoeff p /
              (4 * (p : ℝ) * √r)) *
                MomentDuhamel.momNorm (Gauss.P d) (2 * p) Zgood =
              normGoodCrossBudget E D deltaWeight s t N k p a r := by
          rfl
        rw [hrewrite]
        calc
          normGoodCrossBudget E D deltaWeight s t N k p a r +
                (APrimeGeneralMovingCrossHcrossPositive.crossMomentCoeff p /
                  (4 * (p : ℝ) * √r)) *
                  MomentDuhamel.momNorm (Gauss.P d) (2 * p) Zbad =
              (APrimeGeneralMovingCrossHcrossPositive.crossMomentCoeff p /
                (4 * (p : ℝ) * √r)) *
                  MomentDuhamel.momNorm (Gauss.P d) (2 * p) Zgood +
                (APrimeGeneralMovingCrossHcrossPositive.crossMomentCoeff p /
                  (4 * (p : ℝ) * √r)) *
                  MomentDuhamel.momNorm (Gauss.P d) (2 * p) Zbad := by
                    rw [hrewrite]
          _ ≤ (APrimeGeneralMovingCrossHcrossPositive.crossMomentCoeff p /
                (4 * (p : ℝ) * √r)) *
                  MomentDuhamel.momNorm (Gauss.P d) (2 * p) Zgood +
                (15 * (p : ℝ) / 8) * (N : ℝ) ^ (-(1 : ℝ)) / √r :=
                    add_le_add_right hbadBudget _
          _ = normGoodCrossBudget E D deltaWeight s t N k p a r +
                (15 * (p : ℝ) / 8) * (N : ℝ) ^ (-(1 : ℝ)) / √r := by
                  rw [hrewrite]

/-! The inherited explicit witness has `E=0`, `D=60`, positive scheduled
`deltaWeight`, and eventually an active positive-time `k=2` cell containing a
sample in the literal strict transition event. -/

noncomputable abbrev nondegenerate_active_k2_witness :=
  APrimeGeneralMovingCrossBudgetNormBadAllOrders.nondegenerate_active_k2_witness

#print axioms eventually_positiveTimeCrossBudget_le_normGood_add_normBad
#print axioms nondegenerate_active_k2_witness

end
end RBM.APrimeGeneralMovingCrossBudgetGoodReduction
