/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeCrossJointSplit
import RBM1D.Gauss.APrimeGeneralMovingSmoothQVProfile

/-!
# T606: transition support for the buffered general-moving QV profile

This module turns membership in the literal smooth transition into positivity
of the actual smooth weight at order one, then applies T603 on the identical
sample.  The transition cutoff exponent and the buffered QV-cap exponent
remain distinct.
-/

namespace RBM.APrimeGeneralMovingTransitionQV

open Filter Set Gauss Step2Bootstrap CutHypTheta

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Gauss.Ω d) := band d

private theorem cutChi_pos_of_one_lt_of_lt_two {x : Real}
    (h1 : 1 < x) (h2 : x < 2) : 0 < Cutoff.cutChi x := by
  have ht0 : 0 < x - 1 := by linarith
  have hm1 : max (x - 1) 0 = x - 1 := max_eq_left ht0.le
  have hm2 : max (x - 2) 0 = 0 := max_eq_right (by linarith)
  rw [Cutoff.cutChi, hm1, hm2]
  have hid :
      1 - (6 * (x - 1) ^ 5 - 15 * (x - 1) ^ 4 + 10 * (x - 1) ^ 3) =
        (1 - (x - 1)) ^ 3 * (1 + 3 * (x - 1) + 6 * (x - 1) ^ 2) := by
    ring
  rw [hid]
  have hleft : 0 < (1 - (x - 1)) ^ 3 := pow_pos (by linarith) _
  have hright : 0 < 1 + 3 * (x - 1) + 6 * (x - 1) ^ 2 := by
    nlinarith [sq_nonneg (x - 1)]
  positivity

/-- On the literal T579 common event and literal smooth transition at
`deltaWeight`, the current QV obeys T590's complete absorbed profile with
buffered cap exponent `deltaWeight + xi`.  The statement is pointwise on
closed positive cells and has no moment-order parameter. -/
theorem eventually_qv_le_absorbed_on_smooth_transition_buffered
    {E D c : Real} {s t : Nat -> Real}
    (hE : |E| < 2) (hD : 60 <= D)
    (hs0 : forall N, 0 <= s N)
    (hst : forall N, s N <= t N)
    (ht1 : forall N, t N < 1)
    (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore (Gauss.sample d) E s)
    {zetaSrc zetaCtr tauG deltaWeight xi : Real}
    (hzetaSrc : 0 < zetaSrc)
    (hzetaCtr : 0 < zetaCtr)
    (htauG : 0 < tauG)
    (hxi : 0 < xi)
    (hdeltaCap : 0 < deltaWeight + xi)
    (hzetaTau : zetaSrc <= tauG)
    (htauCap : tauG <= (deltaWeight + xi) / 16)
    (hcapC : deltaWeight + xi <= c / 20)
    (hcapRoom : tauG + 2 * (deltaWeight + xi) + (2 : Real) / 15 < 1) :
    ∀ᶠ N : Nat in Filter.atTop, forall k : Nat,
      1 <= k ->
      k <= CutHypTheta.cutNetTop s t
        (APrimeGeneralMovingMesh.targetMesh D) N ->
      ∀ omega ∈
        APrimeGeneralMovingCommonSources.commonEvent
          E D s t zetaSrc zetaCtr tauG N,
      omega ∈ APrimeCrossJointSplit.transition d E D deltaWeight s
        (APrimeGeneralMovingMesh.targetMesh D) N k
        (APrimeSmoothWeightActual.canonicalM d s t
          (APrimeGeneralMovingMesh.targetMesh D) N) ->
      ∀ u ∈ Set.Icc (s N)
        (CutHypTheta.cutNetPt s
          (APrimeGeneralMovingMesh.targetMesh D) N k),
      forall a : LoopArg (d.L N) 2,
        let v := CutHypTheta.cutNetPt s
          (APrimeGeneralMovingMesh.targetMesh D) N k
        let Jbar := APrimeGeneralMovingQVProfile.generalMovingBlockCap
          E s tauG (deltaWeight + xi) N u
        APrimeDriftTimeFamily.qvAt d E D N Step2.sigPM a
            (s N) v u omega <=
          (APrimeGeneralMovingQVAbsorption.absorbedRootProfile
            E s zetaSrc N u v D Jbar a) ^ 2 := by
  have hqv :=
    RBM.APrimeGeneralMovingSmoothQVProfile.eventually_qv_le_absorbed_on_actual_smooth_support
        hE hD hs0 hst ht1 hc hreg hB hzetaSrc hzetaCtr htauG hxi
        hdeltaCap hzetaTau htauCap hcapC hcapRoom 1 (by norm_num)
  filter_upwards [hqv, eventually_ge_atTop 2] with N hqvN hN2
  intro k hk hkTop omega homega htransition u hu a
  have hactual :
      0 < APrimeSmoothWeightActual.weight d E D deltaWeight s t
        (APrimeGeneralMovingMesh.targetMesh D) 2 1 N k
        (APrimeSmoothWeightActual.canonicalM d s t
          (APrimeGeneralMovingMesh.targetMesh D) N) omega := by
    unfold APrimeSmoothWeightActual.weight
    rw [if_pos ⟨hkTop, hN2⟩]
    exact pow_pos
      (cutChi_pos_of_one_lt_of_lt_two htransition.1 htransition.2) _
  exact (hqvN k hk hkTop omega homega hactual u hu a).2

#print axioms eventually_qv_le_absorbed_on_smooth_transition_buffered

end
end RBM.APrimeGeneralMovingTransitionQV
