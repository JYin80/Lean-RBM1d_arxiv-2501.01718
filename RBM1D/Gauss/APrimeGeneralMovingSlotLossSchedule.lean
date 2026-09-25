/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingSmoothQVProfile

/-!
# T995: loss parameters coupled to the A-prime small slot

For each chosen small-slot exponent `δ`, this file records an explicit
positive loss schedule with the T590/T603 buffer rooms and strict near-slot
exponent room.  It also gives a same-sample, positive actual-smooth-weight
resident on a genuine `E = 0`, `D = 60` moving window.  No integrated profile
fit or A-prime conclusion is asserted.
-/

namespace RBM.APrimeGeneralMovingSlotLossSchedule

open Filter MeasureTheory Set Gauss Step2Bootstrap CutHypTheta

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Gauss.Ω d) := band d

/-- The explicit T995 loss schedule, all losses being selected after `δ`. -/
noncomputable def deltaWeight (δ : Real) : Real := δ / 100
noncomputable def xi (δ : Real) : Real := δ / 100
noncomputable def deltaCap (δ : Real) : Real := δ / 50
noncomputable def tauG (δ : Real) : Real := δ / 1600
noncomputable def zetaSrc (δ : Real) : Real := δ / 3200
noncomputable def zetaCtr (δ : Real) : Real := δ / 3200

/-- Exact real-arithmetic verification of every T590/T603 room and both
strict near-slot exponent gaps.  The hypothesis is the task's small-slot
range `0 < δ ≤ min (1, c/100)`. -/
theorem schedule_room {δ c : Real} (_hc : 0 < c) (hδ : 0 < δ)
    (hsmall : δ ≤ min 1 (c / 100)) :
    0 < deltaWeight δ ∧ 0 < xi δ ∧ 0 < deltaCap δ ∧
    0 < tauG δ ∧ 0 < zetaSrc δ ∧ 0 < zetaCtr δ ∧
    deltaWeight δ + xi δ = deltaCap δ ∧
    zetaSrc δ ≤ tauG δ ∧
    tauG δ ≤ deltaCap δ / 16 ∧
    deltaCap δ ≤ c / 20 ∧
    tauG δ + 2 * deltaCap δ + (2 : Real) / 15 < 1 ∧
    zetaSrc δ / 2 < 5 * δ / 32 ∧
    zetaSrc δ + zetaCtr δ < 5 * δ / 32 := by
  have hδ1 : δ ≤ 1 := hsmall.trans (min_le_left _ _)
  have hδc : δ ≤ c / 100 := hsmall.trans (min_le_right _ _)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [deltaWeight]; positivity
  · dsimp [xi]; positivity
  · dsimp [deltaCap]; positivity
  · dsimp [tauG]; positivity
  · dsimp [zetaSrc]; positivity
  · dsimp [zetaCtr]; positivity
  · dsimp [deltaWeight, xi, deltaCap]; ring
  · dsimp [zetaSrc, tauG]; linarith
  · dsimp [tauG, deltaCap]; nlinarith
  · dsimp [deltaCap]; nlinarith [_hc]
  · dsimp [tauG, deltaCap]; nlinarith
  · dsimp [zetaSrc]; nlinarith
  · dsimp [zetaSrc, zetaCtr]; nlinarith

/-- The accepted T579 common-support witness supports every positive loss
schedule.  For each admissible `δ`, one sample in the literal common event
has widened weight one and strictly positive actual smooth weight at the
same `deltaWeight`, target mesh, first positive cell, and `p = 1`. -/
theorem scheduled_positive_cell_witness :
    ∃ c : Real, 0 < c ∧ ∃ s t : Nat → Real,
      (∀ N, s N = 0) ∧ (∀ N, 0 ≤ s N) ∧ (∀ N, s N ≤ t N) ∧
      (∀ N, t N < 1) ∧
      Cond272Reg B 0 s t c ∧
      BoundsCore (Gauss.sample d) 0 s ∧
      Step1.Hyp (Gauss.sample d) 0 s t ∧
      ∀ δ : Real, 0 < δ → δ ≤ min 1 (c / 100) →
        ∀ᶠ N : Nat in atTop,
          s N < t N ∧
          ∃ ω,
            ω ∈ APrimeGeneralMovingCommonSources.commonEvent
              0 60 s t (zetaSrc δ) (zetaCtr δ) (tauG δ) N ∧
            1 ≤ cutNetTop s t
              (APrimeGeneralMovingMesh.targetMesh 60) N ∧
            APrimeWeight.widenedW
              (APrimeWeight.canonicalR s t
                (APrimeGeneralMovingMesh.targetMesh 60)) 1
              (fun N u ω => Step2Moment.jSnorm
                (Gauss.sample d) 0 60 s N u ω)
              s t (APrimeGeneralMovingMesh.targetMesh 60)
              (deltaWeight δ) 1 N 1 ω = 1 ∧
            0 < APrimeSmoothWeightActual.weight d 0 60
              (deltaWeight δ) s t (APrimeGeneralMovingMesh.targetMesh 60)
              2 1 N 1
              (APrimeSmoothWeightActual.canonicalM d s t
                (APrimeGeneralMovingMesh.targetMesh 60) N) ω := by
  obtain ⟨_tauPrime, _htauPrime, c, hc, s, t, hsEq, hs0, hst, ht1,
      hreg, hB, hStep, hw⟩ :=
    APrimeGeneralMovingCommonSources.positive_length_common_support_witness
  refine ⟨c, hc, s, t, hsEq, hs0, hst, ht1, hreg, hB, hStep, ?_⟩
  intro δ hδ hsmall
  have hroom := schedule_room hc hδ hsmall
  rcases hroom with ⟨hdw, hxi, hcap, htau, hsrc, hctr, hbuffer,
      hsrcTau, htauCap, hcapC, hcapRoom, _, _⟩
  have hresident := hw (zetaSrc δ) (zetaCtr δ) (tauG δ)
    (deltaWeight δ) hsrc hctr htau hdw
  filter_upwards [hresident] with N hN
  obtain ⟨hwindow, ω, hω, hactive, hwide⟩ := hN
  have hwideOne :
      APrimeWeight.widenedW
        (APrimeWeight.canonicalR s t
          (APrimeGeneralMovingMesh.targetMesh 60)) 1
        (fun N u ω => Step2Moment.jSnorm
          (Gauss.sample d) 0 60 s N u ω)
        s t (APrimeGeneralMovingMesh.targetMesh 60)
        (deltaWeight δ) 1 N 1 ω = 1 := by
    simpa only [APrimeGeneralMovingDetFields.J] using hwide 1
  have hcompare := APrimeSmoothWeightActual.widenedW_le_weight_canonical d
    (E := 0) (D := 60) (δ := deltaWeight δ)
    (s := s) (t := t) (mesh := APrimeGeneralMovingMesh.targetMesh 60)
    (by norm_num) hdw.le N 1 1 ω (hst N) (ht1 N)
    (APrimeGeneralMovingMesh.targetMesh_pos 60 N)
  have hwidePos :
      0 < APrimeWeight.widenedW
        (APrimeWeight.canonicalR s t
          (APrimeGeneralMovingMesh.targetMesh 60)) 1
        (fun N u ω => Step2Moment.jSnorm
          (Gauss.sample d) 0 60 s N u ω)
        s t (APrimeGeneralMovingMesh.targetMesh 60)
        (deltaWeight δ) 1 N 1 ω := by
    rw [hwideOne]
    norm_num
  exact ⟨hwindow, ω, hω, hactive, hwideOne, hwidePos.trans_le hcompare⟩

#print axioms schedule_room
#print axioms scheduled_positive_cell_witness

end
end RBM.APrimeGeneralMovingSlotLossSchedule
