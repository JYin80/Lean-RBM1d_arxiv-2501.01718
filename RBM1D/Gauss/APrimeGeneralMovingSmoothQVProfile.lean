/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingQVAbsorption
import RBM1D.Gauss.APrimeSmoothToWidenedSupport

/-!
# T603: buffered actual-smooth support for the general-moving QV profile

This module composes the deterministic support bridge from T599 at
`deltaWeight` with the absorbed positive-cell QV profile from T590 at
`deltaWeight + xi`.  The target mesh, prefix, sample, and common event are
unchanged.
-/

namespace RBM.APrimeGeneralMovingSmoothQVProfile

open Filter MeasureTheory Set Gauss Step2Bootstrap CutHypTheta

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Gauss.Ω d) := band d

/-- On the literal T579 common event, positivity of the actual smooth weight
at `deltaWeight` supplies the buffered widened support at
`deltaWeight + xi`, and hence the complete T590 absorbed QV profile.  The
statement is pointwise on closed positive cells; `k = 0` is intentionally not
part of this theorem. -/
theorem eventually_qv_le_absorbed_on_actual_smooth_support
    {E D c : Real} {s t : Nat -> Real}
    (hE : |E| < 2) (hD : 60 <= D)
    (hs0 : forall N, 0 <= s N) (hst : forall N, s N <= t N)
    (ht1 : forall N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore (Gauss.sample d) E s)
    {zetaSrc zetaCtr tauG deltaWeight xi : Real}
    (hzetaSrc : 0 < zetaSrc) (hzetaCtr : 0 < zetaCtr)
    (htauG : 0 < tauG) (hxi : 0 < xi)
    (hdeltaCap : 0 < deltaWeight + xi)
    (hzetaTau : zetaSrc <= tauG)
    (htauDeltaCap : tauG <= (deltaWeight + xi) / 16)
    (hdeltaCapC : deltaWeight + xi <= c / 20)
    (hcapRoom : tauG + 2 * (deltaWeight + xi) + (2 : Real) / 15 < 1)
    (p : Nat) (hp : 1 <= p) :
    ∀ᶠ N : Nat in atTop, forall k : Nat,
      1 <= k ->
      k <= cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N ->
      ∀ omega ∈ APrimeGeneralMovingCommonSources.commonEvent
          E D s t zetaSrc zetaCtr tauG N,
      0 < APrimeSmoothWeightActual.weight d E D deltaWeight s t
        (APrimeGeneralMovingMesh.targetMesh D) 2 p N k
        (APrimeSmoothWeightActual.canonicalM d s t
          (APrimeGeneralMovingMesh.targetMesh D) N) omega ->
      ∀ u ∈ Set.Icc (s N)
          (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k),
      forall a : LoopArg (d.L N) 2,
        let v := cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k
        let Jbar := APrimeGeneralMovingQVProfile.generalMovingBlockCap
          E s tauG (deltaWeight + xi) N u
        APrimeJG.jG (Gauss.sample d) E N u omega
            (B.ell N u) (etaT E u) D <= Jbar /\
        APrimeDriftTimeFamily.qvAt d E D N Step2.sigPM a (s N) v u omega <=
          (APrimeGeneralMovingQVAbsorption.absorbedRootProfile
            E s zetaSrc N u v D Jbar a) ^ 2 := by
  have hsupport :=
    RBM.APrimeSmoothToWidenedSupport.eventually_actualWeight_pos_implies_widenedW_pos
        d (D := D) (delta := deltaWeight) (xi := xi) hE hst ht1
        (APrimeGeneralMovingMesh.targetMesh_pos D) hxi p hp
  have hqv :=
    RBM.APrimeGeneralMovingQVAbsorption.eventually_qv_le_absorbed_on_common_support
        hE hD hs0 hst ht1 hc hreg hB hzetaSrc hzetaCtr htauG hdeltaCap
        hzetaTau htauDeltaCap hdeltaCapC hcapRoom p hp
  filter_upwards [hsupport, hqv] with N hsupportN hqvN
  intro k hk hkTop omega homega hactual
  have hwide := hsupportN k hkTop omega hactual
  exact hqvN k hk hkTop omega homega hwide

/-- The numerical and regularity assumptions of the buffered theorem are
jointly satisfiable on a nonzero moving window.  This witness deliberately
makes no claim that the common event intersects positive actual-smooth support
on a positive cell; no upstream theorem currently proves that intersection is
inhabited. -/
theorem buffered_absorption_hypotheses_witness :
    exists c : Real, exists s t : Nat -> Real,
      exists deltaWeight xi tauG zetaSrc zetaCtr : Real,
      |(0 : Real)| < 2 /\ (60 : Real) <= 60 /\ (1 : Nat) <= 1 /\
      0 < c /\ 0 < xi /\ 0 < deltaWeight + xi /\
      0 < tauG /\ 0 < zetaSrc /\ 0 < zetaCtr /\
      zetaSrc <= tauG /\
      tauG <= (deltaWeight + xi) / 16 /\
      deltaWeight + xi <= c / 20 /\
      tauG + 2 * (deltaWeight + xi) + (2 : Real) / 15 < 1 /\
      (forall N, s N = 0) /\
      (forall N, 0 <= s N) /\
      (forall N, s N <= t N) /\
      (forall N, t N < 1) /\
      Cond272Reg B 0 s t c /\
      BoundsCore (Gauss.sample d) 0 s /\
      ∀ᶠ N : Nat in atTop, s N < t N := by
  obtain ⟨c, s, t, deltaCap, tauG, zetaSrc, zetaCtr,
      hc, hdeltaCap, htauG, hzetaSrc, hzetaCtr,
      hzetaTau, htauDeltaCap, hdeltaCapC, hcapRoom,
      hsEq, hs0, hst, ht1, hreg, hB, hnondegenerate⟩ :=
    RBM.APrimeGeneralMovingQVAbsorption.positive_cell_absorption_hypotheses_witness
  let deltaWeight : Real := deltaCap / 2
  let xi : Real := deltaCap / 2
  have hxi : 0 < xi := by
    dsimp [xi]
    linarith
  have hsum : deltaWeight + xi = deltaCap := by
    dsimp [deltaWeight, xi]
    ring
  refine ⟨c, s, t, deltaWeight, xi, tauG, zetaSrc, zetaCtr,
    by norm_num, by norm_num, by norm_num, hc, hxi, ?_, htauG,
    hzetaSrc, hzetaCtr, hzetaTau, ?_, ?_, ?_,
    hsEq, hs0, hst, ht1, hreg, hB, ?_⟩
  · simpa only [hsum] using hdeltaCap
  · simpa only [hsum] using htauDeltaCap
  · simpa only [hsum] using hdeltaCapC
  · simpa only [hsum] using hcapRoom
  · filter_upwards [hnondegenerate] with N hN
    exact hN.1

/-- The buffered hypotheses have a genuine same-resident positive-cell
realization.  At `E = 0`, `D = 60`, `p = 1`, and `k = 1`, one sample belongs
to the literal common event, has canonical widened weight exactly one at
`deltaWeight`, and therefore has positive literal actual smooth weight at the
same exponent, mesh, net index, and sample. -/
theorem same_resident_positive_cell_actual_weight_witness :
    exists c : Real, exists s t : Nat -> Real,
      exists deltaCap deltaWeight xi tauG zetaSrc zetaCtr : Real,
      |(0 : Real)| < 2 /\ (60 : Real) <= 60 /\ (1 : Nat) <= 1 /\
      0 < c /\ 0 < deltaCap /\
      deltaWeight = deltaCap / 2 /\ xi = deltaCap / 2 /\
      0 <= deltaWeight /\ 0 < xi /\ deltaWeight + xi = deltaCap /\
      0 < tauG /\ 0 < zetaSrc /\ 0 < zetaCtr /\
      zetaSrc <= tauG /\ tauG <= deltaCap / 16 /\ deltaCap <= c / 20 /\
      tauG + 2 * deltaCap + (2 : Real) / 15 < 1 /\
      (forall N, s N = 0) /\
      (forall N, 0 <= s N) /\
      (forall N, s N <= t N) /\
      (forall N, t N < 1) /\
      (forall N, 0 < APrimeGeneralMovingMesh.targetMesh 60 N) /\
      Cond272Reg B 0 s t c /\
      BoundsCore (Gauss.sample d) 0 s /\
      ∀ᶠ N : Nat in atTop,
        s N < t N /\
        exists omega,
          omega ∈ APrimeGeneralMovingCommonSources.commonEvent
            0 60 s t zetaSrc zetaCtr tauG N /\
          1 <= cutNetTop s t
            (APrimeGeneralMovingMesh.targetMesh 60) N /\
          APrimeWeight.widenedW
              (APrimeWeight.canonicalR s t
                (APrimeGeneralMovingMesh.targetMesh 60)) 1
              (fun N u omega => Step2Moment.jSnorm
                (Gauss.sample d) 0 60 s N u omega)
              s t (APrimeGeneralMovingMesh.targetMesh 60)
              deltaWeight 1 N 1 omega = 1 /\
          0 < APrimeSmoothWeightActual.weight d 0 60 deltaWeight s t
            (APrimeGeneralMovingMesh.targetMesh 60) 2 1 N 1
            (APrimeSmoothWeightActual.canonicalM d s t
              (APrimeGeneralMovingMesh.targetMesh 60) N) omega := by
  obtain ⟨_tauPrime, _htauPrime, c, hc, s, t, hsEq, hs0, hst, ht1,
      hreg, hB, _hStep, hw⟩ :=
    APrimeGeneralMovingCommonSources.positive_length_common_support_witness
  let deltaCap : Real := min (c / 40) (1 / 100)
  let deltaWeight : Real := deltaCap / 2
  let xi : Real := deltaCap / 2
  let tauG : Real := deltaCap / 32
  let zetaSrc : Real := tauG / 2
  let zetaCtr : Real := tauG / 2
  have hdeltaCap : 0 < deltaCap := by
    dsimp [deltaCap]
    exact lt_min (by positivity) (by norm_num)
  have hdeltaWeight : 0 < deltaWeight := by
    dsimp [deltaWeight]
    positivity
  have hxi : 0 < xi := by
    dsimp [xi]
    positivity
  have hsum : deltaWeight + xi = deltaCap := by
    dsimp [deltaWeight, xi]
    ring
  have htauG : 0 < tauG := by dsimp [tauG]; positivity
  have hzetaSrc : 0 < zetaSrc := by dsimp [zetaSrc]; positivity
  have hzetaCtr : 0 < zetaCtr := by dsimp [zetaCtr]; positivity
  have hzetaTau : zetaSrc <= tauG := by dsimp [zetaSrc]; linarith
  have htauCap : tauG <= deltaCap / 16 := by dsimp [tauG]; linarith
  have hcapC : deltaCap <= c / 20 := by
    have hdc : deltaCap <= c / 40 := min_le_left _ _
    linarith
  have hcapSmall : deltaCap <= 1 / 100 := min_le_right _ _
  have hcapRoom : tauG + 2 * deltaCap + (2 : Real) / 15 < 1 := by
    dsimp [tauG]
    linarith
  have hresident := hw zetaSrc zetaCtr tauG deltaWeight
    hzetaSrc hzetaCtr htauG hdeltaWeight
  refine ⟨c, s, t, deltaCap, deltaWeight, xi, tauG, zetaSrc, zetaCtr,
    by norm_num, by norm_num, by norm_num, hc, hdeltaCap, rfl, rfl,
    hdeltaWeight.le, hxi, hsum, htauG, hzetaSrc, hzetaCtr, hzetaTau,
    htauCap, hcapC, hcapRoom, hsEq, hs0, hst, ht1,
    APrimeGeneralMovingMesh.targetMesh_pos 60, hreg, hB, ?_⟩
  filter_upwards [hresident] with N hN
  obtain ⟨hwindow, omega, homega, hactive, hwide⟩ := hN
  have hwideOne :
      APrimeWeight.widenedW
          (APrimeWeight.canonicalR s t
            (APrimeGeneralMovingMesh.targetMesh 60)) 1
          (fun N u omega => Step2Moment.jSnorm
            (Gauss.sample d) 0 60 s N u omega)
          s t (APrimeGeneralMovingMesh.targetMesh 60)
          deltaWeight 1 N 1 omega = 1 := by
    simpa only [APrimeGeneralMovingDetFields.J] using hwide 1
  have hcompare := APrimeSmoothWeightActual.widenedW_le_weight_canonical d
    (E := 0) (D := 60) (δ := deltaWeight)
    (s := s) (t := t) (mesh := APrimeGeneralMovingMesh.targetMesh 60)
    (by norm_num) hdeltaWeight.le N 1 1 omega
    (hst N) (ht1 N) (APrimeGeneralMovingMesh.targetMesh_pos 60 N)
  have hwidePos :
      0 < APrimeWeight.widenedW
          (APrimeWeight.canonicalR s t
            (APrimeGeneralMovingMesh.targetMesh 60)) 1
          (fun N u omega => Step2Moment.jSnorm
            (Gauss.sample d) 0 60 s N u omega)
          s t (APrimeGeneralMovingMesh.targetMesh 60)
          deltaWeight 1 N 1 omega := by
    rw [hwideOne]
    norm_num
  exact ⟨hwindow, omega, homega, hactive, hwideOne,
    hwidePos.trans_le hcompare⟩

#print axioms eventually_qv_le_absorbed_on_actual_smooth_support
#print axioms buffered_absorption_hypotheses_witness
#print axioms same_resident_positive_cell_actual_weight_witness

end
end RBM.APrimeGeneralMovingSmoothQVProfile
