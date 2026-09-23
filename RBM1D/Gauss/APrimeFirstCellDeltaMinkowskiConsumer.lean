/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellDeltaFullCrossBudget
import RBM1D.Gauss.APrimeFirstCellTimeIntegrability
import RBM1D.Gauss.APrimeAssembly

/-!
# T556: variable-delta exact first-cell Minkowski consumer

This file integrates an explicitly supplied pointwise derivative bound.  The
canonical weight, actual coordinate, actual drift, literal full-cross rate,
and uncut quadratic variation all retain the caller's `delta`.
-/

namespace RBM.APrimeFirstCellDeltaMinkowskiConsumer

open Filter MeasureTheory Set Gauss CutHypTheta
open RBM.MomentDuhamel

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

noncomputable def canonicalM (tauPrime : Real) (N : Nat) : Nat :=
  APrimeSmoothWeightActual.canonicalM d (fun _ => 0) (firstCellT tauPrime)
    APrimeSmoothTransition.transitionMesh N

noncomputable def endpoint (N k : Nat) : Real :=
  cutNetPt (fun _ => 0) APrimeSmoothTransition.transitionMesh N k

noncomputable def weight (tauPrime delta : Real) (p N k : Nat) : Ω d -> Real :=
  APrimeSmoothWeightActual.weight d 0 60 delta (fun _ => 0)
    (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh
    2 p N k (canonicalM tauPrime N)

noncomputable def Y (N k : Nat) (a : LoopArg (d.L N) 2)
    (r : Real) : Ω d -> Real :=
  APrimeDuhamelModel.flowY d N
    (APrimeDriftTimeFamily.coordAt d 0 60 N Step2.sigPM a 0 (endpoint N k)) r

noncomputable def A (tauPrime delta : Real) (p N k : Nat)
    (a : LoopArg (d.L N) 2) (r : Real) : Real :=
  momNormW (P d) (weight tauPrime delta p N k) p
    (APrimeDriftTimeFamily.driftAt d 0 60 N Step2.sigPM a 0
      (endpoint N k) r)

noncomputable def B (tauPrime delta alpha : Real)
    (p N k : Nat) (r : Real) : Real :=
  APrimeFirstCellDeltaFullCrossBudget.literalBfull
    tauPrime delta alpha p N (endpoint N k) r

noncomputable def g (tauPrime delta : Real) (p N k : Nat)
    (a : LoopArg (d.L N) 2) (r : Real) : Real :=
  APrimeModel.rateNormW (P d) (weight tauPrime delta p N k) p
    (APrimeDriftTimeFamily.qvAt d 0 60 N Step2.sigPM a 0
      (endpoint N k) r)

noncomputable def initial (N k : Nat) (a : LoopArg (d.L N) 2) : Ω d -> Real :=
  APrimeAssembly.initialEvolvedNormAt (sample d) 0 60 (fun _ => 0) N
    (endpoint N k) a

/-- The open pointwise premise, written in the exact literal shape consumed
by the variable-delta derivative producer. -/
def pointwiseDerivativePremiseAt (tauPrime delta alpha : Real)
    (p N k : Nat) (a : LoopArg (d.L N) 2) (r : Real) : Prop :=
  let v := endpoint N k
  let w := weight tauPrime delta p N k
  let Yu := Y N k a r
  let G := APrimeDriftTimeFamily.driftAt
    d 0 60 N Step2.sigPM a 0 v r
  let Q := APrimeDriftTimeFamily.qvAt
    d 0 60 N Step2.sigPM a 0 v r
  APrimeDuhamelModel.momFlowDeriv d N
      (APrimeDriftTimeFamily.momentAt d 0 60 N p Step2.sigPM a 0 v)
      w
      (APrimeSmoothWeightActual.weightD d 0 60 delta (fun _ => 0)
        (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh
        2 p N k (canonicalM tauPrime N)) r <=
    2 * (p : Real) *
        (∫ omega, w omega * |Yu omega| ^ (2 * p) ∂(P d)) ^
          ((2 * (p : Real) - 1) / (2 * (p : Real))) *
        (momNormW (P d) w p G +
          APrimeFirstCellDeltaFullCrossBudget.literalBfull
            tauPrime delta alpha p N v r) +
      (p : Real) * (2 * (p : Real) - 1) *
        (∫ omega, w omega * |Yu omega| ^ (2 * p) ∂(P d)) ^
          (((p : Real) - 1) / (p : Real)) *
        APrimeModel.rateNormW (P d) w p Q

/-- The exact integrated conclusion at one actual moving first-cell output. -/
def minkowskiBoundAt (tauPrime delta alpha : Real) (p N k : Nat)
    (a : LoopArg (d.L N) 2) : Prop :=
  momNormW (P d) (weight tauPrime delta p N k) p (Y N k a (endpoint N k)) <=
    momNormW (P d) (weight tauPrime delta p N k) p (initial N k a) +
      2 * (∫ r in (0 : Real)..endpoint N k,
        (A tauPrime delta p N k a r + B tauPrime delta alpha p N k r)) +
      Real.sqrt ((2 * (p : Real) - 1) *
        ∫ r in (0 : Real)..endpoint N k, g tauPrime delta p N k a r)

theorem Y_zero_eq_initial {N k : Nat} (a : LoopArg (d.L N) 2)
    (hv0 : 0 <= endpoint N k) (hv1 : endpoint N k < 1) :
    Y N k a 0 = initial N k a := by
  funext omega
  have hflow := APrimeDriftTimeFamily.flowY_coordAt d 0 60 N Step2.sigPM a
    (s := 0) (v := endpoint N k) (by norm_num) hv0 hv1 0 omega
  change APrimeDuhamelModel.flowY d N
      (APrimeDriftTimeFamily.coordAt d 0 60 N Step2.sigPM a 0
        (endpoint N k)) 0 omega = _
  rw [hflow]
  rfl

/-- Fixed-size exact Minkowski assembly from the open pointwise derivative
premise. -/
theorem minkowskiBoundAt_of_deriv
    {tauPrime delta alpha : Real} {p N k : Nat}
    (hTau : 0 < tauPrime) (hDelta : 0 < delta) (hAlpha : 0 < alpha)
    (hp : 1 <= p) (hN : 0 < N)
    (hk : k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N)
    (a : LoopArg (d.L N) 2)
    (hbound : ∀ r ∈ Ioc (0 : Real) (endpoint N k),
      pointwiseDerivativePremiseAt tauPrime delta alpha p N k a r) :
    minkowskiBoundAt tauPrime delta alpha p N k a := by
  let v := endpoint N k
  let m := canonicalM tauPrime N
  let w := weight tauPrime delta p N k
  let Psi := APrimeDriftTimeFamily.momentAt
    d 0 60 N p Step2.sigPM a 0 v
  let Psi1 := APrimeDriftTimeFamily.coordAt
    d 0 60 N Step2.sigPM a 0 v
  let wD := APrimeSmoothWeightActual.weightD d 0 60 delta (fun _ => 0)
    (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh
    2 p N k m
  let phi' := APrimeDuhamelModel.momFlowDeriv d N Psi w wD
  have ht := APrimeSupportRunning.firstT_bounds hTau N
  have hv : v ∈ Icc (0 : Real) (firstCellT tauPrime N) := by
    exact MomentDuhamelCut.netFinset_subset_Icc ht.1
      (APrimeSupportRunning.mesh_pos N) _ (cutNetPt_mem_netFinset hk)
  have hv1 : v < 1 := hv.2.trans_lt (ht.2.trans_lt (by norm_num))
  have htest : Gauss.TestFunT₁ d N (Icc (0 : Real) v) Psi := by
    exact APrimeNormalizedTestFun.normalizedTestFunBridge
      d 0 60 N p Step2.sigPM a (by norm_num) (by norm_num) hv.1 hv1
  have hm : 1 <= m := by
    exact APrimeSmoothWeightActual.canonicalM_pos d (fun _ => 0)
      (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh N
  have hu : ∀ j < k, cutNetPt (fun _ => 0)
      APrimeSmoothTransition.transitionMesh N j < 1 := by
    intro j hj
    have hjtop : j <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
        APrimeSmoothTransition.transitionMesh N := by omega
    have hjmem := MomentDuhamelCut.netFinset_subset_Icc ht.1
      (APrimeSupportRunning.mesh_pos N) _ (cutNetPt_mem_netFinset hjtop)
    exact hjmem.2.trans_lt (ht.2.trans_lt (by norm_num))
  have hwC1 : Gauss.WeightC1 d N w wD := by
    dsimp only [w, weight, wD, m, canonicalM]
    exact APrimeSmoothWeightActual.weightC1 d (E := 0) (D := 60)
      (δ := delta) (s := fun _ => 0) (t := firstCellT tauPrime)
      (mesh := APrimeSmoothTransition.transitionMesh) (N₀ := 2)
      (p := p) (N := N) (k := k)
      (m := APrimeSmoothWeightActual.canonicalM d (fun _ => 0)
        (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh N)
      (by norm_num) (by norm_num) hN hm hu
  have hw0 : ∀ omega, 0 <= w omega := by
    intro omega
    dsimp only [w, weight]
    exact APrimeSmoothWeightActual.weight_nonneg d 0 60 delta (fun _ => 0)
      (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh
      2 p N k m omega
  have hw1 : ∀ omega, w omega <= 1 := by
    intro omega
    dsimp only [w, weight]
    exact APrimeSmoothWeightActual.weight_le_one d 0 60 delta (fun _ => 0)
      (firstCellT tauPrime) APrimeSmoothTransition.transitionMesh
      2 p N k m omega
  have hre := APrimeDriftTimeFamily.momentAt_isModulusPow
    d 0 60 N p Step2.sigPM a 0 v
  have hcont := APrimeDuhamelModel.continuousOn_momFlow
    htest hwC1 hre (Set.Subset.rfl : Icc (0 : Real) v ⊆ Icc 0 v)
  have hderiv : ∀ u ∈ Ioo (0 : Real) v,
      HasDerivAt (fun r : Real => ∫ omega,
        w omega * |APrimeDuhamelModel.flowY d N Psi1 r omega| ^ (2 * p) ∂(P d))
        (phi' u) u := by
    intro u huI
    exact APrimeDuhamelModel.hasDerivAt_momFlow htest hwC1 hre huI.1
      (Icc_mem_nhds huI.1 huI.2)
  have hphiInt : IntervalIntegrable phi' volume 0 v := by
    exact APrimeDuhamelModel.intervalIntegrable_momFlowDeriv
      htest hwC1 hre (by norm_num) hv.1 Set.Subset.rfl
  have hA0 : ∀ u ∈ Icc (0 : Real) v,
      0 <= A tauPrime delta p N k a u := by
    intro u huI
    exact momNormW_nonneg (P := P d) hw0 p _
  have hB0 : ∀ u ∈ Icc (0 : Real) v,
      0 <= B tauPrime delta alpha p N k u := by
    intro u huI
    unfold B APrimeFirstCellDeltaFullCrossBudget.literalBfull
    unfold APrimeFirstCellFullCrossIntegrability.Bfull
    have hrate : 0 <= APrimeFirstCellQVCurrentRows.currentRate
        delta (delta / 16) alpha N v u := by
      exact APrimeFirstCellFullCrossIntegrability.currentRate_nonneg
        (by omega) hv.1 (hv.2.trans ht.2) huI
    have hpref : 0 <=
        APrimeFirstCellDeltaFullCrossBudget.prefixRate delta alpha N v :=
      APrimeFirstCellDeltaFullCrossBudget.prefixRate_nonneg hv.1
    have henv : 0 <= APrimeFirstCellCrossBadPayment.jointEnvelope N := by
      unfold APrimeFirstCellCrossBadPayment.jointEnvelope
      positivity
    have hrho : 0 <= APrimeFirstCellCrossBadPayment.rho
        tauPrime delta alpha N := ENNReal.toReal_nonneg
    positivity
  have hg0 : ∀ u ∈ Icc (0 : Real) v,
      0 <= g tauPrime delta p N k a u := by
    intro u huI
    exact APrimeModel.rateNormW_nonneg hw0 p _
  have hpack :=
    APrimeFirstCellTimeIntegrability.actual_weightedMinkowski_integrability
      (δ := delta) (κ := 0) hTau (N₀ := 2) (p := p) (N := N) (k := k)
      hN hp hk a
  have hAint : IntervalIntegrable
      (A tauPrime delta p N k a) volume 0 v := by
    change IntervalIntegrable
      (APrimeFirstCellTimeIntegrability.Adr
        tauPrime delta 2 p N k a) volume 0
      (APrimeFirstCellTimeIntegrability.endpoint N k)
    simpa [APrimeFirstCellTimeIntegrability.Bcr,
      APrimeDriftTimeFamily.crossAt, APrimeModel.crossInt] using hpack.1
  have hBint : IntervalIntegrable
      (B tauPrime delta alpha p N k) volume 0 v := by
    unfold B APrimeFirstCellDeltaFullCrossBudget.literalBfull
    exact (APrimeFirstCellFullCrossIntegrability.intervalIntegrable_Bfull
      hDelta.le hAlpha (by omega) hp hv.1 (hv.2.trans ht.2)
      (APrimeFirstCellDeltaFullCrossBudget.prefixRate_nonneg hv.1)
      (by unfold APrimeFirstCellCrossBadPayment.jointEnvelope; positivity)
      ENNReal.toReal_nonneg).1
  have hABint : IntervalIntegrable
      (fun r => A tauPrime delta p N k a r +
        B tauPrime delta alpha p N k r) volume 0 v := hAint.add hBint
  have hgint : IntervalIntegrable
      (g tauPrime delta p N k a) volume 0 v := by
    change IntervalIntegrable
      (APrimeFirstCellTimeIntegrability.g
        tauPrime delta 2 p N k a) volume 0
      (APrimeFirstCellTimeIntegrability.endpoint N k)
    exact hpack.2.1
  have hprefix : ∀ u ∈ Icc (0 : Real) v,
      IntervalIntegrable (fun r => momNormW (P d) w p
        (APrimeDuhamelModel.flowY d N Psi1 r) *
          (A tauPrime delta p N k a r +
            B tauPrime delta alpha p N k r)) volume 0 u := by
    intro u huI
    exact APrimeTimeIntegrability.intervalIntegrable_momNormW_mul_flowY
      hv.1 Set.Subset.rfl hp htest hwC1 hre hABint huI
  have hMink := weightedMinkowski_of_deriv_le hv.1 hp hw0 hcont hderiv
    hphiInt hA0 hB0 hg0 hABint hgint hprefix (by
      intro u huI
      have hb := hbound u ⟨huI.1, huI.2.le⟩
      simpa [pointwiseDerivativePremiseAt, endpoint, canonicalM, weight, Y,
        A, B, g, v, m, w, Psi, Psi1, wD, phi', d] using hb)
  have hY0 : Y N k a 0 = initial N k a := Y_zero_eq_initial a hv.1 hv1
  have hMinkY : momNormW (P d) w p (Y N k a v) <=
      momNormW (P d) w p (Y N k a 0) +
        2 * (∫ r in (0 : Real)..v,
          (A tauPrime delta p N k a r +
            B tauPrime delta alpha p N k r)) +
        Real.sqrt ((2 * (p : Real) - 1) *
          ∫ r in (0 : Real)..v, g tauPrime delta p N k a r) := by
    simpa [Y, A, B, g, Psi1, d] using hMink
  rw [hY0] at hMinkY
  simpa [minkowskiBoundAt, v, w] using hMinkY

/-- Fixed parameters precede the eventual matrix size. -/
def actualDerivativePremise
    (tauPrime delta alpha : Real) (p : Nat) : Prop :=
  ∀ᶠ N : Nat in atTop, ∀ k, 1 <= k ->
    k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N ->
    ∀ a : LoopArg (d.L N) 2,
      ∀ r ∈ Ioc (0 : Real) (endpoint N k),
        pointwiseDerivativePremiseAt tauPrime delta alpha p N k a r

def actualMinkowskiBound (tauPrime delta alpha : Real) (p : Nat) : Prop :=
  ∀ᶠ N : Nat in atTop, ∀ k, 1 <= k ->
    k <= cutNetTop (fun _ => 0) (firstCellT tauPrime)
      APrimeSmoothTransition.transitionMesh N ->
    ∀ a : LoopArg (d.L N) 2,
      minkowskiBoundAt tauPrime delta alpha p N k a

theorem actualMinkowskiBound_of_deriv
    {tauPrime delta alpha : Real} {p : Nat}
    (hTau : 0 < tauPrime) (hDelta : 0 < delta)
    (hAlpha : 0 < alpha) (hp : 1 <= p)
    (hderiv : actualDerivativePremise tauPrime delta alpha p) :
    actualMinkowskiBound tauPrime delta alpha p := by
  filter_upwards [hderiv, eventually_ge_atTop 1] with N hderivN hN
  intro k hk1 hk a
  exact minkowskiBoundAt_of_deriv hTau hDelta hAlpha hp (by omega) hk a
    (hderivN k hk1 hk a)

/-- The zero mesh index is the exact zero-time branch. -/
theorem minkowskiBoundAt_k_zero (tauPrime delta alpha : Real) (p N : Nat)
    (a : LoopArg (d.L N) 2) :
    endpoint N 0 = 0 ∧ minkowskiBoundAt tauPrime delta alpha p N 0 a := by
  have hv : endpoint N 0 = 0 := by simp [endpoint, cutNetPt_zero]
  have hv0 : 0 <= endpoint N 0 := by rw [hv]
  have hv1 : endpoint N 0 < 1 := by rw [hv]; norm_num
  have hY0 : Y N 0 a 0 = initial N 0 a :=
    Y_zero_eq_initial a hv0 hv1
  constructor
  · exact hv
  · unfold minkowskiBoundAt
    rw [hv, hY0]
    simp

def kZeroMinkowskiBound
    (tauPrime delta alpha : Real) (p : Nat) : Prop :=
  ∀ᶠ N : Nat in atTop, ∀ a : LoopArg (d.L N) 2,
    endpoint N 0 = 0 ∧ minkowskiBoundAt tauPrime delta alpha p N 0 a

theorem eventually_kZeroMinkowskiBound
    (tauPrime delta alpha : Real) (p : Nat) :
    kZeroMinkowskiBound tauPrime delta alpha p := by
  exact Filter.Eventually.of_forall fun N a =>
    minkowskiBoundAt_k_zero tauPrime delta alpha p N a

/-- Direct pointer to the compiled sharp, nonzero satisfiability witness for
the generic weighted Minkowski interface. -/
theorem genericSharpMinkowskiWitness :
    momNormW (P d) (fun _ => (1 : Real)) 1 (fun _ => Real.sqrt (1 : Real)) <=
      momNormW (P d) (fun _ => (1 : Real)) 1 (fun _ => Real.sqrt (0 : Real)) +
        2 * (∫ _r in (0 : Real)..1, ((0 : Real) + 0)) +
        Real.sqrt ((2 * ((1 : Nat) : Real) - 1) *
          ∫ _r in (0 : Real)..1, (1 : Real)) :=
  MomentDuhamel.sat_weightedMinkowski_sharp (P d)

end

end RBM.APrimeFirstCellDeltaMinkowskiConsumer

namespace RBM.APrimeFirstCellDeltaMinkowskiConsumer

#print axioms Y_zero_eq_initial
#print axioms minkowskiBoundAt_of_deriv
#print axioms actualMinkowskiBound_of_deriv
#print axioms minkowskiBoundAt_k_zero
#print axioms eventually_kZeroMinkowskiBound
#print axioms genericSharpMinkowskiWitness

end RBM.APrimeFirstCellDeltaMinkowskiConsumer
