/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingJointRateIntegrable
import RBM1D.Gauss.APrimeGeneralMovingJointRateNormBadPayment

/-!
# T1197: exact norm-good/norm-bad decomposition of the joint-rate moment

For each fixed positive integer moment order, the exact full Gaussian moment
of the literal general-moving joint rate splits into its restrictions to the
T100 norm-good event and its complement.  Integrability is supplied by T1035;
the statement is an equality only, with no estimate on either part.
-/

namespace RBM.APrimeGeneralMovingJointRateMomentEventSplit

open Filter MeasureTheory Set Gauss CutHypTheta
open scoped Matrix.Norms.L2Operator

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev mesh (D : ℝ) : ℕ → ℝ :=
  APrimeGeneralMovingMesh.targetMesh D

/-- The T100 spectral-norm good event, shared with T1173. -/
noncomputable abbrev normGood (N : ℕ) : Set (Ω d) :=
  APrimeGeneralMovingJointRateNormBadPayment.normGood N

/-- For every fixed `p ≥ 1`, one eventual cutoff works uniformly over the
active target-mesh prefixes, outputs, and closed-cell running times, with the
consumer's fixed `Step2.sigPM` charge:
the full Gaussian `2p` moment of the literal joint rate equals the sum of
its restrictions to the norm-good event and its complement. -/
theorem eventually_jointRate_pow_integral_eq_normGood_add_normBad
    {E D c : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg (band d) E s t c)
    {deltaWeight : ℝ} (hdeltaWeight : 0 ≤ deltaWeight)
    (p : ℕ) (hp : 1 ≤ p) :
    ∀ᶠ N : ℕ in atTop,
      ∀ k ≤ cutNetTop s t (mesh D) N,
      ∀ a : LoopArg (d.L N) 2,
      ∀ u ∈ Icc (s N) (cutNetPt s (mesh D) N k),
        ∫ ω,
          |APrimeCrossJointSplit.jointRate d E D deltaWeight s (mesh D) N k
            (APrimeSmoothWeightActual.canonicalM d s t (mesh D) N)
            Step2.sigPM a (cutNetPt s (mesh D) N k) u ω| ^ (2 * p) ∂(Gauss.P d) =
          (∫ ω in normGood N,
            |APrimeCrossJointSplit.jointRate d E D deltaWeight s (mesh D) N k
              (APrimeSmoothWeightActual.canonicalM d s t (mesh D) N)
              Step2.sigPM a (cutNetPt s (mesh D) N k) u ω| ^ (2 * p) ∂(Gauss.P d)) +
          (∫ ω in (normGood N)ᶜ,
            |APrimeCrossJointSplit.jointRate d E D deltaWeight s (mesh D) N k
              (APrimeSmoothWeightActual.canonicalM d s t (mesh D) N)
              Step2.sigPM a (cutNetPt s (mesh D) N k) u ω| ^ (2 * p) ∂(Gauss.P d)) := by
  have hint :=
    APrimeGeneralMovingJointRateIntegrable.eventually_integrable_jointRate_pow
      hE hD hs0 hst ht1 hc hreg hdeltaWeight p hp
  letI : IsProbabilityMeasure (Gauss.P d) := Gauss.isProbabilityMeasure_P d
  filter_upwards [hint] with N hN
  intro k hk a u hu
  have hGoodMeas : MeasurableSet (normGood N) := by
    simpa [normGood,
      APrimeGeneralMovingJointRateNormBadPayment.normGood] using
        Gauss.measurableSet_normX_le d N
  have hsplit := integral_add_compl hGoodMeas (hN k hk Step2.sigPM a u hu)
  simpa [normGood] using hsplit.symm

/-! T1173's nondegenerate active-`k=2` witness is re-exported verbatim. -/

noncomputable abbrev nondegenerate_first_cell_active_k2_witness :=
  APrimeGeneralMovingJointRateNormBadPayment.nondegenerate_first_cell_active_k2_witness

#print axioms eventually_jointRate_pow_integral_eq_normGood_add_normBad
#print axioms nondegenerate_first_cell_active_k2_witness

end
end RBM.APrimeGeneralMovingJointRateMomentEventSplit
