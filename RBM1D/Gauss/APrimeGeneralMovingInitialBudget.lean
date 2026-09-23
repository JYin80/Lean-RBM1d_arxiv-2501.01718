/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingInitialHinit
import RBM1D.Gauss.APrimeGeneralMovingMesh
import RBM1D.Gauss.APrimeSmoothWeightActual

/-!
# T600: actual smooth-weight initial budget on a general moving window

The endpoint-uniform T488 estimate is invoked once with the constant weight
one.  Only after its eventual threshold has been fixed do we choose an active
target-net index and dominate the literal actual smooth prefix weight by one.

This file treats only the initial Duhamel term.  It supplies no first-cell
producer, event or support statement, generator, moment family, A-prime slot,
or closure claim.
-/

namespace RBM.APrimeGeneralMovingInitialBudget

open Filter MeasureTheory Set Gauss CutHypTheta
open RBM.MomentDuhamel

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

/-- The active target-net point, carrying its proof of membership in the
closed moving time interval. -/
noncomputable def targetCutNetPt {s t : Nat -> Real} (D : Real)
    (hst : forall N, s N <= t N) (N k : Nat)
    (hk : k <= cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N) :
    TimeIcc s t N :=
  ⟨cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k,
    MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _
      (cutNetPt_mem_netFinset hk)⟩

/-- The zeroth target-net subtype is exactly the moving left endpoint. -/
@[simp] theorem targetCutNetPt_zero {s t : Nat -> Real} (D : Real)
    (hst : forall N, s N <= t N) (N : Nat)
    (hk : 0 <= cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N) :
    (targetCutNetPt D hst N 0 hk : Real) = s N := by
  simp [targetCutNetPt, cutNetPt_zero]

/-- The literal actual smooth weight has empty prefix, hence equals one, at
the zeroth target-net index. -/
theorem smoothWeight_zero (E D delta : Real) (s t : Nat -> Real)
    (p N : Nat) (omega : Ω d) :
    APrimeSmoothWeightActual.weight d E D delta s t
      (APrimeGeneralMovingMesh.targetMesh D) 2 p N 0
      (APrimeSmoothWeightActual.canonicalM d s t
        (APrimeGeneralMovingMesh.targetMesh D) N) omega = 1 := by
  exact APrimeSmoothWeightActual.weight_zero_prefix d E D delta s t
    (APrimeGeneralMovingMesh.targetMesh D) 2 p N
    (APrimeSmoothWeightActual.canonicalM d s t
      (APrimeGeneralMovingMesh.targetMesh D) N)
    (APrimeSmoothWeightActual.canonicalM_pos d s t
      (APrimeGeneralMovingMesh.targetMesh D) N) omega

/-- Domination of a nonnegative weight by one decreases the weighted moment
norm.  Integrability of the unweighted absolute moment is the only analytic
input. -/
private theorem momNormW_le_one_weight {Omega' : Type*} [MeasurableSpace Omega']
    (P' : Measure Omega') (w Y : Omega' -> Real) (p : Nat)
    (hw0 : forall omega, 0 <= w omega) (hw1 : forall omega, w omega <= 1)
    (hint : Integrable (fun omega => |Y omega| ^ (2 * p)) P') :
    momNormW P' w p Y <= momNormW P' (fun _ => 1) p Y := by
  have hi : (∫ omega, w omega * |Y omega| ^ (2 * p) ∂P') <=
      ∫ omega, |Y omega| ^ (2 * p) ∂P' := by
    apply integral_mono_of_nonneg
      (Eventually.of_forall fun omega => mul_nonneg (hw0 omega) (by positivity)) hint
    exact Eventually.of_forall fun omega =>
      mul_le_of_le_one_left (by positivity) (hw1 omega)
  unfold momNormW
  simp only [one_mul]
  exact Real.rpow_le_rpow
    (integral_nonneg fun omega => mul_nonneg (hw0 omega) (by positivity)) hi
    (by positivity)

/-- One eventual threshold controls the literal net-indexed actual smooth
weight at every active target-mesh endpoint and every two-loop coordinate.
The endpoint and the `R_v ^ 4` normalization are unchanged from T488. -/
theorem eventually_initial_hinit_smooth_target
    {E D c delta : Real} {s t : Nat -> Real}
    (hE : |E| < 2) (hD : 60 <= D)
    (hs0 : forall N, 0 <= s N)
    (hst : forall N, s N <= t N)
    (ht1 : forall N, t N < 1)
    (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore (sample d) E s)
    (hdelta : 0 < delta) (p : Nat) (hp : 1 <= p) :
    ∀ᶠ N : Nat in atTop, forall k,
      forall hk : k <= cutNetTop s t
        (APrimeGeneralMovingMesh.targetMesh D) N,
      forall a : LoopArg (d.L N) 2,
        momNormW B.P
          (APrimeSmoothWeightActual.weight d E D delta s t
            (APrimeGeneralMovingMesh.targetMesh D) 2 p N k
            (APrimeSmoothWeightActual.canonicalM d s t
              (APrimeGeneralMovingMesh.targetMesh D) N))
          p
          (APrimeAssembly.initialEvolvedNormAt (sample d) E D s N
            (targetCutNetPt D hst N k hk) a) <=
          APrimeOneStep.initTerm ((N : Real) ^ (delta / 8))
            (etaT E (s N) / etaT E (targetCutNetPt D hst N k hk))
            (APrimeInit.slotXi' ((N : Real) ^ (delta / 8))) /
          (etaT E (s N) / etaT E (targetCutNetPt D hst N k hk)) ^ 4 := by
  have hone := APrimeGeneralMovingInitialHinit.eventually_initial_hinit
    (E := E) (D := D) (c := c) (δ := delta) (s := s) (t := t)
    hE hD hs0 hst ht1 hc hreg hB hdelta p hp
    (fun _ _ _ => 1) (fun _ _ => aestronglyMeasurable_const)
    (fun _ _ _ => zero_le_one) (fun _ _ _ => le_rfl)
  filter_upwards [hone] with N hN
  intro k hk a
  let v : TimeIcc s t N := targetCutNetPt D hst N k hk
  have hint := APrimeAssembly.integrable_initialEvolvedNormAt_pow_gauss d
    hE hs0 hst ht1 p N v D a
  have hmono := momNormW_le_one_weight B.P
    (APrimeSmoothWeightActual.weight d E D delta s t
      (APrimeGeneralMovingMesh.targetMesh D) 2 p N k
      (APrimeSmoothWeightActual.canonicalM d s t
        (APrimeGeneralMovingMesh.targetMesh D) N))
    (APrimeAssembly.initialEvolvedNormAt (sample d) E D s N v a) p
    (fun omega => APrimeSmoothWeightActual.weight_nonneg d E D delta s t
      (APrimeGeneralMovingMesh.targetMesh D) 2 p N k
      (APrimeSmoothWeightActual.canonicalM d s t
        (APrimeGeneralMovingMesh.targetMesh D) N) omega)
    (fun omega => APrimeSmoothWeightActual.weight_le_one d E D delta s t
      (APrimeGeneralMovingMesh.targetMesh D) 2 p N k
      (APrimeSmoothWeightActual.canonicalM d s t
        (APrimeGeneralMovingMesh.targetMesh D) N) omega)
    hint
  exact hmono.trans (hN (v, a))

/-- The assumptions of the smooth target-budget theorem have a simultaneous
nondegenerate realization on a genuinely positive-length moving window. -/
theorem positive_length_assumptions_witness :
    exists (E D c delta : Real) (p : Nat) (s t : Nat -> Real),
      |E| < 2 ∧ 60 <= D ∧
      (forall N, 0 <= s N) ∧ (forall N, s N <= t N) ∧
      (forall N, t N < 1) ∧ 0 < c ∧ Cond272Reg B E s t c ∧
      BoundsCore (sample d) E s ∧ 0 < delta ∧ 1 <= p ∧
      (∀ᶠ N : Nat in atTop, s N < t N) := by
  obtain ⟨tauPrime, _hTau, c, hc, hsEq, hs0, hst, ht1, hreg, hB, hpos⟩ :=
    APrimeGeneralMovingInitialHinit.positive_length_hinit_witness
  let s : Nat -> Real := fun N => gridT ((B.W N : Real)) tauPrime (1 / 2 : Real) 0
  let t : Nat -> Real := fun N => gridT ((B.W N : Real)) tauPrime (1 / 2 : Real) 1
  change (forall N, s N = 0) at hsEq
  change (forall N, 0 <= s N) at hs0
  change (forall N, s N <= t N) at hst
  change (forall N, t N < 1) at ht1
  change Cond272Reg B 0 s t c at hreg
  change BoundsCore (sample d) 0 s at hB
  change ∀ᶠ N : Nat in atTop, s N < t N at hpos
  exact ⟨0, 60, c, 1 / 2, 1, s, t, by norm_num, by norm_num,
    hs0, hst, ht1, hc, hreg, hB, by norm_num, by norm_num, hpos⟩

#print axioms targetCutNetPt
#print axioms targetCutNetPt_zero
#print axioms smoothWeight_zero
#print axioms eventually_initial_hinit_smooth_target
#print axioms positive_length_assumptions_witness

end
end RBM.APrimeGeneralMovingInitialBudget
