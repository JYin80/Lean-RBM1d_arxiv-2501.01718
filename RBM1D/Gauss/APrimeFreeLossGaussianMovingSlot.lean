/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFreeLossGaussianCoordinateProducer
import RBM1D.Gauss.APrimeFreeLossMovingSlotAdapter

/-!
# T1335: Gaussian moving-window A-prime slot

Compose the audited Gaussian moving-family producer with the conditional
moving-window slot adapter. The positive-window witness retains the complete
family premise, adapter output, and T1331's same-sample common-event resident.
This is scoped to the actual `Dims.exampleGrow` Gaussian observables; it does
not formalize the stopped hierarchy in (5.21), (5.24), or (5.40)--(5.43).
-/

namespace RBM.APrimeFreeLossGaussianMovingSlot

open Filter MeasureTheory Set Gauss CutHypTheta Step2Bootstrap
open scoped Matrix.Norms.L2Operator

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev mesh (D : ℝ) : ℕ → ℝ :=
  APrimeGeneralMovingMesh.targetMesh D

/-- The exact widened-family premise consumed by T1321, with the positive
loss range supplied by T1331. -/
theorem moving_hfamily_of_gaussian_hypotheses
    {E D c : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg (Gauss.band d) E s t c)
    (hB : BoundsCore (Gauss.sample d) E s) :
    ∀ δ : ℝ, 0 < δ → δ ≤ min (1 / 10000) (c / 10000) →
      ∀ p : ℕ, ∃ C > (0 : ℝ),
        ∀ᶠ N : ℕ in atTop, ∀ k : ℕ,
          k ≤ cutNetTop s t (mesh D) N →
          ∫ ω, APrimeWeight.widenedW
              (APrimeWeight.canonicalR s t (mesh D)) 1
              (fun N u ω => Step2Moment.jSnorm (Gauss.sample d) E D s N u ω)
              s t (mesh D) δ p N k ω *
            |MomentDuhamelCut.cutTrunc ((N : ℝ) ^ (2 * δ))
              (Step2Moment.jSnorm (Gauss.sample d) E D s N
                (cutNetPt s (mesh D) N k) ω)| ^ (2 * p)
            ∂(Gauss.band d).P ≤ C * (N : ℝ) ^ (δ / 2 * (p : ℝ)) := by
  simpa [APrimeFreeLossFamilyBridge.targetWeight,
    APrimeFreeLossFamilyBridge.targetJ] using
    APrimeFreeLossGaussianCoordinateProducer.moving_hfamily_of_gaussian_hypotheses
      hE hD hs0 hst ht1 hc hreg hB

/-- The actual Gaussian moving-window `APrimeSlot'`, obtained by composing
T1331's exact widened-family conclusion with T1321's conditional adapter. -/
noncomputable def slot_of_gaussian_hypotheses
    {E D c : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg (Gauss.band d) E s t c)
    (hB : BoundsCore (Gauss.sample d) E s) :
    APrimeSlotFields.APrimeSlot' (Gauss.sample d) E s t D := by
  let δ₀ : ℝ := min (1 / 10000) (c / 10000)
  have hδ₀ : 0 < δ₀ := by
    dsimp [δ₀]
    exact lt_min (by norm_num) (by positivity)
  have hfamily :
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ p : ℕ,
        ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
          ∀ k ≤ cutNetTop s t (mesh D) N,
            ∫ ω, APrimeWeight.widenedW
                (APrimeWeight.canonicalR s t (mesh D)) 1
                (fun N u ω => Step2Moment.jSnorm (Gauss.sample d) E D s N u ω)
                s t (mesh D) δ p N k ω *
              |MomentDuhamelCut.cutTrunc ((N : ℝ) ^ (2 * δ))
                (Step2Moment.jSnorm (Gauss.sample d) E D s N
                  (cutNetPt s (mesh D) N k) ω)| ^ (2 * p)
              ∂(Gauss.band d).P ≤ C * (N : ℝ) ^ (δ / 2 * (p : ℝ)) := by
    simpa [δ₀] using
      moving_hfamily_of_gaussian_hypotheses
        hE hD hs0 hst ht1 hc hreg hB
  exact APrimeFreeLossMovingSlotAdapter.slot_of_widened_family
    hE hD hs0 hst ht1 hc hreg hδ₀ hfamily

/-- Structured nonvacuity data for one positive-length Gaussian window.
`hfamily` is the exact premise of the moving-slot adapter, and `slot_eq`
records that `slot` is its output for that same premise. -/
structure PositiveWindowSlotWitness (c : ℝ) (s t : ℕ → ℝ) where
  hE : |(0 : ℝ)| < 2
  hD : (60 : ℝ) ≤ 60
  hsEq : ∀ N, s N = 0
  hs0 : ∀ N, 0 ≤ s N
  hst : ∀ N, s N ≤ t N
  ht1 : ∀ N, t N < 1
  hc : 0 < c
  hreg : Cond272Reg (Gauss.band d) 0 s t c
  hB : BoundsCore (Gauss.sample d) 0 s
  hStep : Step1.Hyp (Gauss.sample d) 0 s t
  hcoordinate :
    APrimeFreeLossFamilyBridge.UniformSameActualCoordinateInput 0 60 c s t
  hfamily :
    ∀ δ : ℝ, 0 < δ → δ ≤ min (1 / 10000) (c / 10000) →
      ∀ p : ℕ, ∃ C > (0 : ℝ),
        ∀ᶠ N : ℕ in atTop, ∀ k : ℕ,
          k ≤ cutNetTop s t (mesh 60) N →
          ∫ ω, APrimeWeight.widenedW
              (APrimeWeight.canonicalR s t (mesh 60)) 1
              (fun N u ω => Step2Moment.jSnorm (Gauss.sample d) 0 60 s N u ω)
              s t (mesh 60) δ p N k ω *
            |MomentDuhamelCut.cutTrunc ((N : ℝ) ^ (2 * δ))
              (Step2Moment.jSnorm (Gauss.sample d) 0 60 s N
                (cutNetPt s (mesh 60) N k) ω)| ^ (2 * p)
            ∂(Gauss.band d).P ≤ C * (N : ℝ) ^ (δ / 2 * (p : ℝ))
  hδ₀ : 0 < min (1 / 10000) (c / 10000)
  slot : APrimeSlotFields.APrimeSlot' (Gauss.sample d) 0 s t 60
  slot_eq : slot = APrimeFreeLossMovingSlotAdapter.slot_of_widened_family
    hE hD hs0 hst ht1 hc hreg hδ₀ hfamily
  resident :
    ∀ loss : ℝ, 0 < loss → loss ≤ min (1 / 10000) (c / 10000) →
      ∀ᶠ N : ℕ in atTop,
        s N < t N ∧ ∃ ω,
          ω ∈ APrimeGeneralMovingCommonSources.commonEvent
            0 60 s t (loss / 1000) (loss / 1000) (loss / 1000) N ∧
          1 ≤ cutNetTop s t (mesh 60) N ∧
          APrimeWeight.widenedW
            (APrimeWeight.canonicalR s t (mesh 60)) 1
            (fun N u ω => Step2Moment.jSnorm (Gauss.sample d) 0 60 s N u ω)
            s t (mesh 60) loss 1 N 1 ω = 1 ∧
          0 < APrimeSmoothWeightActual.weight d 0 60 loss s t
            (mesh 60) 2 1 N 1
            (APrimeSmoothWeightActual.canonicalM d s t (mesh 60) N) ω

/-- A joint nondegenerate `E = 0`, `D = 60` window witnessing all Gaussian
hypotheses, the full exact T1321 widened-family premise, the resulting actual
slot on that same window, and T1331's positive active-cell common-event
resident. -/
theorem positive_window_joint_slot_witness :
    ∃ c : ℝ, 0 < c ∧
    ∃ s t : ℕ → ℝ, Nonempty (PositiveWindowSlotWitness c s t) := by
  obtain ⟨c, hc, s, t, hsEq, hs0, hst, ht1, hreg, hB, hStep, hcoordinate,
      hresident⟩ :=
    APrimeFreeLossGaussianCoordinateProducer.positive_window_full_uniform_coordinate_input_witness
  have hfamily := APrimeFreeLossFamilyBridge.moving_hfamily_of_same_actual_coordinate_input
    (E := 0) (D := 60) (c := c) (s := s) (t := t)
    (by norm_num) hc hs0 hst ht1 hcoordinate
  have hfamily' :
      ∀ δ : ℝ, 0 < δ → δ ≤ min (1 / 10000) (c / 10000) →
        ∀ p : ℕ, ∃ C > (0 : ℝ),
          ∀ᶠ N : ℕ in atTop, ∀ k : ℕ,
            k ≤ cutNetTop s t (mesh 60) N →
            ∫ ω, APrimeWeight.widenedW
                (APrimeWeight.canonicalR s t (mesh 60)) 1
                (fun N u ω => Step2Moment.jSnorm (Gauss.sample d) 0 60 s N u ω)
                s t (mesh 60) δ p N k ω *
              |MomentDuhamelCut.cutTrunc ((N : ℝ) ^ (2 * δ))
                (Step2Moment.jSnorm (Gauss.sample d) 0 60 s N
                  (cutNetPt s (mesh 60) N k) ω)| ^ (2 * p)
              ∂(Gauss.band d).P ≤ C * (N : ℝ) ^ (δ / 2 * (p : ℝ)) := by
    simpa [APrimeFreeLossFamilyBridge.targetWeight,
      APrimeFreeLossFamilyBridge.targetJ] using hfamily
  have hδ₀ : 0 < min (1 / 10000) (c / 10000) :=
    lt_min (by norm_num) (by positivity)
  let W : PositiveWindowSlotWitness c s t := {
    hE := by norm_num
    hD := by norm_num
    hsEq := hsEq
    hs0 := hs0
    hst := hst
    ht1 := ht1
    hc := hc
    hreg := hreg
    hB := hB
    hStep := hStep
    hcoordinate := hcoordinate
    hfamily := hfamily'
    hδ₀ := hδ₀
    slot := APrimeFreeLossMovingSlotAdapter.slot_of_widened_family
      (E := 0) (D := 60) (c := c) (δ₀ := min (1 / 10000) (c / 10000))
      (s := s) (t := t) (by norm_num) (by norm_num) hs0 hst ht1 hc hreg hδ₀ hfamily'
    slot_eq := rfl
    resident := hresident }
  exact ⟨c, hc, s, t, ⟨W⟩⟩

#print axioms moving_hfamily_of_gaussian_hypotheses
#print axioms slot_of_gaussian_hypotheses
#print axioms positive_window_joint_slot_witness

end

end RBM.APrimeFreeLossGaussianMovingSlot
