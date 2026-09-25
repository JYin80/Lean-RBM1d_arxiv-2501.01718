/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFreeLossFamilyBridge
import RBM1D.Gauss.APrimeFreeLossDriftCrossBudget
import RBM1D.Gauss.APrimeFreeLossN1SlotFit
import RBM1D.Gauss.APrimeFreeLossQVSlotProducer
import RBM1D.Gauss.APrimeFreeLossCoordinateBridge

/-!
# T1331: Gaussian producer for the corrected-loss uniform coordinate input

For the actual `Dims.exampleGrow` Gaussian model, the accepted quantitative
actual-drift/full-cross producer feeds the exact all-cell N1 slot consumer;
the accepted actual-QV producer supplies N2.  The conditional coordinate
bridge then gives T1307's full same-actual-weight coordinate input, with its
loss and moment order fixed before the eventual cutoff.  The final theorem
applies T1307's conditional moving-family bridge without changing its target.

This is a Gaussian smooth-prefix coordinate result.  It does not close the
paper's stopped hierarchy or identify the Lean observable with the literal
stopped process in (5.21), (5.24), and (5.40)--(5.43).
-/

namespace RBM.APrimeFreeLossGaussianCoordinateProducer

open Filter MeasureTheory Set Gauss CutHypTheta Step2Bootstrap
open scoped Matrix.Norms.L2Operator NNReal

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d
private noncomputable abbrev mesh (D : ℝ) : ℕ → ℝ :=
  APrimeGeneralMovingMesh.targetMesh D

/-- The conditional T1323 coordinate producer composed with the exact T1327
N1 and T1329 N2 producers yields the full T1307 input.  The order `q` is
chosen from the requested loss and `p` before taking the eventual cutoff. -/
theorem uniform_same_actual_coordinate_input_of_gaussian_hypotheses
    {E D c : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore (Gauss.sample d) E s) :
    APrimeFreeLossFamilyBridge.UniformSameActualCoordinateInput E D c s t := by
  intro loss hloss hsmall p hp
  let q : ℕ := max p (Nat.ceil (16 / loss))
  have hqbound : max p (Nat.ceil (16 / loss)) ≤ q := by
    dsimp [q]
    exact le_rfl
  have hq : 1 ≤ q := by
    dsimp [q]
    exact le_trans hp (Nat.le_max_left _ _)
  obtain ⟨C, hC, hbudget⟩ :=
    APrimeFreeLossDriftCrossBudget.exists_positive_C_eventually_actual_drift_plus_full_cross_hbudget
      (E := E) (D := D) (c := c) (lambda := loss) (s := s) (t := t)
      hE hD hs0 hst ht1 hc hreg hB hloss hsmall q hq
  have hN1slots :=
    APrimeFreeLossN1SlotFit.eventually_actual_driftCross_le_driftSlot
      q hq hE hD hs0 hst ht1 hc hreg hloss hC hbudget
  have hN1 : ∀ᶠ N : ℕ in atTop, ∀ k : ℕ,
      k ≤ cutNetTop s t (mesh D) N →
      ∀ a : LoopArg (d.L N) 2,
        APrimeFreeLossCoordinateBridge.LiteralN1Slot E D loss s t q N k a := by
    filter_upwards [hN1slots] with N hN1slotsN
    intro k hk a
    have hslot := (hN1slotsN k hk a).2.2
    simpa [APrimeFreeLossCoordinateBridge.LiteralN1Slot,
      APrimeFreeLossCoordinateBridge.endpoint,
      APrimeGeneralMovingAllOrdersMinkowskiActual.endpoint, mesh] using hslot
  have hN2producer :=
    APrimeFreeLossQVSlotProducer.eventually_literal_n2_slot_of_actual_qv_integral
      (E := E) (D := D) (c := c) (lambda := loss) (s := s) (t := t)
      (q := q) hE hD hs0 hst ht1 hc hreg hB hloss hsmall hq
  have hN2 : ∀ᶠ N : ℕ in atTop, ∀ k : ℕ,
      k ≤ cutNetTop s t (mesh D) N →
      ∀ a : LoopArg (d.L N) 2,
        APrimeFreeLossCoordinateBridge.LiteralN2Slot E D loss s t q N k a := by
    filter_upwards [hN2producer] with N hN2producerN
    intro k hk a
    have hslot := hN2producerN k hk a
    simpa [APrimeFreeLossCoordinateBridge.LiteralN2Slot,
      APrimeFreeLossCoordinateBridge.endpoint,
      APrimeGeneralMovingAllOrdersMinkowskiActual.endpoint, mesh] using hslot
  obtain ⟨C₀, hC₀, hcoordinate⟩ :=
    APrimeFreeLossCoordinateBridge.eventually_same_actual_coordinate_moment_of_literal_slots
      (E := E) (D := D) (c := c) (loss := loss) (s := s) (t := t)
      hE hD hs0 hst ht1 hc hreg hB hloss hsmall hq hN1 hN2
  refine ⟨q, hqbound, C₀, hC₀, ?_⟩
  filter_upwards [hcoordinate] with N hcoordinateN
  intro k hk
  exact hcoordinateN k hk

/-- Exact T1307 moving-family conclusion, obtained by applying its conditional
coordinate-to-family bridge to the Gaussian coordinate producer above. -/
theorem moving_hfamily_of_gaussian_hypotheses
    {E D c : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore (Gauss.sample d) E s) :
    ∀ δ : ℝ, 0 < δ → δ ≤ min (1 / 10000) (c / 10000) →
      ∀ p : ℕ, ∃ C > (0 : ℝ),
        ∀ᶠ N : ℕ in atTop, ∀ k : ℕ,
          k ≤ cutNetTop s t (mesh D) N →
          ∫ ω, APrimeFreeLossFamilyBridge.targetWeight E D δ s t p N k ω *
            |MomentDuhamelCut.cutTrunc ((N : ℝ) ^ (2 * δ))
              (APrimeFreeLossFamilyBridge.targetJ E D s N
                (cutNetPt s (mesh D) N k) ω)| ^ (2 * p)
            ∂(Gauss.band d).P ≤ C * (N : ℝ) ^ (δ / 2 * (p : ℝ)) := by
  exact APrimeFreeLossFamilyBridge.moving_hfamily_of_same_actual_coordinate_input
    hE hc hs0 hst ht1
    (uniform_same_actual_coordinate_input_of_gaussian_hypotheses
      hE hD hs0 hst ht1 hc hreg hB)

/-- A single nondegenerate E=0, D=60 Gaussian window supports the *full*
quantitative T1307 coordinate input for every admissible positive loss and
order, and has a same-sample common-event resident with a positive actual
weight on a positive-length window and active positive cell. -/
theorem positive_window_full_uniform_coordinate_input_witness :
    ∃ c : ℝ, 0 < c ∧
    ∃ s t : ℕ → ℝ,
      (∀ N, s N = 0) ∧
      (∀ N, 0 ≤ s N) ∧
      (∀ N, s N ≤ t N) ∧
      (∀ N, t N < 1) ∧
      Cond272Reg B 0 s t c ∧
      BoundsCore (Gauss.sample d) 0 s ∧
      Step1.Hyp (Gauss.sample d) 0 s t ∧
      APrimeFreeLossFamilyBridge.UniformSameActualCoordinateInput 0 60 c s t ∧
      ∀ loss : ℝ, 0 < loss → loss ≤ min (1 / 10000) (c / 10000) →
        ∀ᶠ N : ℕ in atTop,
          s N < t N ∧ ∃ ω,
            ω ∈ APrimeGeneralMovingCommonSources.commonEvent
              0 60 s t (loss / 1000) (loss / 1000) (loss / 1000) N ∧
            1 ≤ cutNetTop s t (mesh 60) N ∧
            APrimeWeight.widenedW
              (APrimeWeight.canonicalR s t (mesh 60)) 1
              (fun N u ω => Step2Moment.jSnorm (Gauss.sample d)
                0 60 s N u ω)
              s t (mesh 60) loss 1 N 1 ω = 1 ∧
            0 < APrimeSmoothWeightActual.weight d 0 60 loss s t
              (mesh 60) 2 1 N 1
              (APrimeSmoothWeightActual.canonicalM d s t (mesh 60) N) ω := by
  obtain ⟨c, hc, s, t, hsEq, hs0, hst, ht1, hreg, hB, hStep, hresident⟩ :=
    APrimeFreeLossCoordinateBridge.nondegenerate_gaussian_geometry_witness
  have hcoordinate :=
    uniform_same_actual_coordinate_input_of_gaussian_hypotheses
      (E := 0) (D := 60) (c := c) (s := s) (t := t)
      (by norm_num) (by norm_num) hs0 hst ht1 hc hreg hB
  exact ⟨c, hc, s, t, hsEq, hs0, hst, ht1, hreg, hB, hStep,
    hcoordinate, hresident⟩

#print axioms uniform_same_actual_coordinate_input_of_gaussian_hypotheses
#print axioms moving_hfamily_of_gaussian_hypotheses
#print axioms positive_window_full_uniform_coordinate_input_witness

end
end RBM.APrimeFreeLossGaussianCoordinateProducer
