/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingCommonSources
import RBM1D.Gauss.APrimeCrossJointSplit

/-!
# T597: general-moving support on the actual smooth transition

On the literal T579 common-event sample, membership in the actual smooth
transition bounds every stored prefix value.  The existing general-moving
modulus and target-mesh estimate then propagate this bound to the closed
running prefix, without using support of the target widened weight.
-/

namespace RBM.APrimeGeneralMovingSmoothTransitionSupport

open Filter MeasureTheory Set Gauss Step2Bootstrap CutHypTheta

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

/-- A stored normalized-loop value is one of the entries in the actual
smooth prefix sample.  This is the arbitrary-energy, arbitrary-window form
of the comparison used by the first-cell transition argument. -/
private theorem jSnorm_net_le_prefixSample
    {E D : Real} {s mesh : Nat → Real} {N k m j : Nat}
    (hE : |E| < 2) (hs1 : s N < 1) (hN : 0 < N) (hm : 1 <= m)
    (hj : j < k) (hu : cutNetPt s mesh N j < 1) (omega : Ω d) :
    Step2Moment.jSnorm (sample d) E D s N (cutNetPt s mesh N j) omega <=
      APrimeSmoothWeightActual.prefixSample d E D s mesh N k m omega := by
  have hinner := APrimeSmoothPrefix.jSnorm_le_smoothJS d (D := D) hE hs1 hu
    (APrimeSmoothWeightActual.epsilon_pos d D hN).le hm omega
  have heq : APrimeSmoothWeightActual.prefixSample d E D s mesh N k m omega =
      softMax m (Finset.range k) (fun i =>
        APrimeSmoothPrefix.smoothJS d E D s N (cutNetPt s mesh N i)
          (APrimeSmoothWeightActual.epsilon d D N) m omega) := by
    unfold APrimeSmoothWeightActual.prefixSample
      APrimeSmoothWeightActual.prefixMatrix
    apply congrArg (fun f : Nat → Real => softMax m (Finset.range k) f)
    funext i
    exact APrimeSmoothPrefix.smoothJSMatrix_flow d E D s N
      (cutNetPt s mesh N i) (APrimeSmoothWeightActual.epsilon d D N) m omega
  rw [heq]
  exact hinner.trans ((le_abs_self _).trans
    (le_softMax hm
      (ρ := fun i => APrimeSmoothPrefix.smoothJS d E D s N
        (cutNetPt s mesh N i) (APrimeSmoothWeightActual.epsilon d D N) m omega)
      (Finset.mem_range.mpr hj)))

/-- On the same sample in T579's literal common event and in the actual
smooth transition, the normalized loop stays below the exact transition
cap on the whole closed prefix.  The positive-prefix condition excludes the
empty prefix `k = 0`, while both time endpoints remain included. -/
theorem eventually_running_cap_on_smooth_transition
    {E D c delta zetaSrc zetaCtr tauG : Real}
    {s t : Nat → Real}
    (hE : |E| < 2) (hD : 60 <= D)
    (hs0 : forall N, 0 <= s N)
    (hst : forall N, s N <= t N)
    (ht1 : forall N, t N < 1)
    (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    (hdelta : 0 < delta) :
    ∀ᶠ N : Nat in atTop, ∀ k : Nat,
      1 <= k →
      k <= cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N →
      ∀ omega ∈
        APrimeGeneralMovingCommonSources.commonEvent
          E D s t zetaSrc zetaCtr tauG N,
      omega ∈ APrimeCrossJointSplit.transition d E D delta s
        (APrimeGeneralMovingMesh.targetMesh D) N k
        (APrimeSmoothWeightActual.canonicalM d s t
          (APrimeGeneralMovingMesh.targetMesh D) N) →
      ∀ u ∈ Set.Icc (s N)
          (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k),
        APrimeGeneralMovingDetFields.J E D s N u omega <=
          (16 * (Real.exp 1)^2 + 1) * (N : Real)^(2 * delta) := by
  let H := APrimeGeneralMovingDetFields.detFieldPackage
    hE hD hs0 hst ht1 hc hreg
  filter_upwards [H.modulus, H.mesh_fine, eventually_ge_atTop 1]
    with N hmod hfine hN
  intro k hk hkTop omega homega htransition u hu
  let mesh := APrimeGeneralMovingMesh.targetMesh D
  let J := APrimeGeneralMovingDetFields.J E D s
  let m := APrimeSmoothWeightActual.canonicalM d s t mesh N
  let cap := 16 * (Real.exp 1)^2 * (N : Real)^(2 * delta)
  have hNpos : 0 < N := by omega
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  have hm : 1 <= m := by
    exact APrimeSmoothWeightActual.canonicalM_pos d s t mesh N
  have hCarrier :=
    APrimeGeneralMovingCommonSources.commonEvent_subset_rawCarrier
      E D s t zetaSrc zetaCtr tauG N homega
  have hGood : omega ∈ APrimeGeneralMovingGoodMesh.good N :=
    APrimeGeneralMovingRawSources.sourceGood_subset_good
      E s t zetaSrc N hCarrier.1.1.1
  have hprefix :
      APrimeSmoothWeightActual.prefixSample d E D s mesh N k m omega < cap := by
    have hratio := htransition.2
    have hthreshold := APrimeSmoothWeightActual.threshold_pos
      (δ := delta) hNpos
    have hlt : APrimeSmoothWeightActual.prefixSample d E D s mesh N k m omega <
        2 * APrimeSmoothWeightActual.threshold delta N :=
      (div_lt_iff₀ hthreshold).mp hratio
    have heq : 2 * APrimeSmoothWeightActual.threshold delta N = cap := by
      dsimp [APrimeSmoothWeightActual.threshold, cap]
      ring
    exact heq ▸ hlt
  have hnet : ∀ j < k, J N (cutNetPt s mesh N j) omega <= cap := by
    intro j hj
    have huIcc : cutNetPt s mesh N j ∈ Set.Icc (s N) (t N) :=
      MomentDuhamelCut.netFinset_subset_Icc (hst N) (H.mesh_pos N) _
        (cutNetPt_mem_netFinset (hj.le.trans hkTop))
    have hstored := jSnorm_net_le_prefixSample (D := D) hE hs1 hNpos hm hj
      (huIcc.2.trans_lt (ht1 N)) omega
    exact hstored.trans hprefix.le
  have hbase := prefix_of_modulus
    (s := s) (t := t) (mesh := mesh)
    (Kmod := APrimeGeneralMovingFieldPackage.Kmod D)
    (γ := APrimeGeneralMovingFieldPackage.gamma)
    (thr := 1) (c := cap) H.gamma_pos (H.window N) (H.mesh_pos N)
    hk hkTop (hmod omega hGood) hfine hnet u hu
  have hNreal : (1 : Real) <= N := by exact_mod_cast hN
  have hpow : 1 <= (N : Real)^(2 * delta) :=
    Real.one_le_rpow hNreal (by linarith)
  dsimp [J, cap] at hbase ⊢
  have hexp : 0 < Real.exp 1 := Real.exp_pos 1
  nlinarith

/-- The window and common-event side of the support theorem are nondegenerate
at the explicit parameter point `E = 0`, `D = 60`, and source exponents one:
eventually there is a common-event sample and the prefix `k = 1` is active.
This statement deliberately makes no claim that this sample also belongs to
the strict smooth transition. -/
theorem positive_length_common_event_witness :
    ∃ c : Real, 0 < c ∧ ∃ s t : Nat → Real,
      (∀ N, 0 ≤ s N) ∧
      (∀ N, s N ≤ t N) ∧
      (∀ N, t N < 1) ∧
      Cond272Reg B 0 s t c ∧
      ∀ᶠ N : Nat in atTop,
        s N < t N ∧
        ∃ omega ∈ APrimeGeneralMovingCommonSources.commonEvent
            0 60 s t 1 1 1 N,
          1 ≤ cutNetTop s t
            (APrimeGeneralMovingMesh.targetMesh 60) N := by
  obtain ⟨_tauPrime, _htauPrime, c, hc, s, t, _hsEq, hs0, hst, ht1,
      hreg, _hB, _hStep, hcommon⟩ :=
    APrimeGeneralMovingCommonSources.positive_length_common_support_witness
  refine ⟨c, hc, s, t, hs0, hst, ht1, hreg, ?_⟩
  have h := hcommon 1 1 1 1 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  filter_upwards [h] with N hN
  obtain ⟨hpos, omega, homega, hactive, _hwide⟩ := hN
  exact ⟨hpos, omega, homega, hactive⟩

#print axioms eventually_running_cap_on_smooth_transition
#print axioms positive_length_common_event_witness

end
end RBM.APrimeGeneralMovingSmoothTransitionSupport
