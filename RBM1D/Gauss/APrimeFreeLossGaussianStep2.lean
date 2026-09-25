/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFreeLossGaussianMovingSlot
import RBM1D.Flow.Step1Producer

/-!
# T1337: the local Gaussian Step-2 composition

Compose the accepted T1335 moving Gaussian `APrimeSlot'` with the exact
`jsNormDom_of_aprimeSlot'`, `step1Hyp_slot`, and `step2_of_jsNormDom` interfaces.
The decay profile includes the floor `W^{-D}` inside `decayProf`; see the
corresponding paper delta recorded in the T1337 report.
-/

namespace RBM.Gauss.APrimeFreeLossGaussianStep2

open Filter MeasureTheory

private noncomputable abbrev d : Dims := Dims.exampleGrow

/-- The T1335 actual Gaussian moving slot supplies the exact `JSNormDom`
premise required by the existing Step-2 consumer, at every `D ≥ 60`. -/
theorem jsNormDom_of_gaussian_hypotheses
    {κ E c : ℝ} {s t : ℕ → ℝ}
    (hκ0 : 0 < κ) (hEκ : |E| ≤ 2 - κ)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hc : 0 < c) (hreg : Cond272Reg (Gauss.band d) E s t c)
    (hB : BoundsCore (Gauss.sample d) E s) :
    ∀ D : ℝ, 60 ≤ D → APrimeModel.JSNormDom (Gauss.sample d) E s t D := by
  have hE : |E| < 2 := by linarith
  intro D hD
  have hslot := APrimeFreeLossGaussianMovingSlot.slot_of_gaussian_hypotheses
    hE hD hs0 hst ht1 hc hreg hB
  exact APrimeSlotFields.jsNormDom_of_aprimeSlot' hslot hE hst ht1
    hreg.1 hB (by linarith)

/-- Actual Gaussian Step 2 on a moving window, with the exact conclusion of
`APrimeModel.step2_of_jsNormDom`. -/
theorem step2_of_gaussian_hypotheses
    {κ E c : ℝ} {s t : ℕ → ℝ}
    (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hEκ : |E| ≤ 2 - κ)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hc : 0 < c) (hreg : Cond272Reg (Gauss.band d) E s t c)
    (hB : BoundsCore (Gauss.sample d) E s) :
    StochDom (Gauss.band d).P
      (fun N (p : TimeIcc s t N × ((Gauss.band d).Idx N × (Gauss.band d).Idx N)) ω =>
        (Gauss.sample d).llErr E N p.1 ω p.2)
      (fun N p _ => ((Gauss.band d).scale E N p.1)⁻¹ ^ ((1 : ℝ) / 2)) ∧
    ∀ D : ℝ, 0 < D → StochDom (Gauss.band d).P
      (fun N (p : TimeIcc s t N ×
          (ZMod ((Gauss.band d).L N) × ZMod ((Gauss.band d).L N))) ω =>
        (Gauss.sample d).lkErr E N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => (etaT E (s N) / etaT E p.1) ^ 4 *
        ((Gauss.band d).scale E N p.1)⁻¹ ^ 2 *
        (Gauss.band d).decayProf N p.1 D p.2.1 p.2.2) := by
  have h1 : Step1.Hyp (Gauss.sample d) E s t :=
    Gauss.step1Hyp_slot d hκ0 E hEκ s t hs0 hst ht1 c hc hreg hB
  exact APrimeModel.step2_of_jsNormDom (Gauss.sample d) hκ0 hκ1 hEκ
    (jsNormDom_of_gaussian_hypotheses hκ0 hEκ hs0 hst ht1 hc hreg hB)
    h1 hB hs0 hst ht1 hc hreg.1 hreg.2

/-- Same-window nondegeneracy data retaining T1335's full family premise,
the Step-1 hypothesis, and the positive active-cell common-event resident,
as well as the resulting `JSNormDom` and Step-2 conclusion. -/
structure PositiveWindowStep2Witness (c : ℝ) (s t : ℕ → ℝ) where
  base : APrimeFreeLossGaussianMovingSlot.PositiveWindowSlotWitness c s t
  step1 : Step1.Hyp (Gauss.sample d) 0 s t
  jsNorm : ∀ D : ℝ, 60 ≤ D →
    APrimeModel.JSNormDom (Gauss.sample d) 0 s t D
  step2 :
    StochDom (Gauss.band d).P
      (fun N (p : TimeIcc s t N ×
          ((Gauss.band d).Idx N × (Gauss.band d).Idx N)) ω =>
        (Gauss.sample d).llErr 0 N p.1 ω p.2)
      (fun N p _ => ((Gauss.band d).scale 0 N p.1)⁻¹ ^ ((1 : ℝ) / 2)) ∧
    ∀ D : ℝ, 0 < D → StochDom (Gauss.band d).P
      (fun N (p : TimeIcc s t N ×
          (ZMod ((Gauss.band d).L N) × ZMod ((Gauss.band d).L N))) ω =>
        (Gauss.sample d).lkErr 0 N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => (etaT 0 (s N) / etaT 0 p.1) ^ 4 *
        ((Gauss.band d).scale 0 N p.1)⁻¹ ^ 2 *
        (Gauss.band d).decayProf N p.1 D p.2.1 p.2.2)

/-- A positive-length, same-sample `E = 0`, `κ = 1`, `D = 60` witness for the
entire T1337 composition. -/
theorem positive_window_joint_step2_witness :
    ∃ c : ℝ, 0 < c ∧ ∃ s t : ℕ → ℝ,
      Nonempty (PositiveWindowStep2Witness c s t) := by
  obtain ⟨c, hc, s, t, ⟨base⟩⟩ :=
    APrimeFreeLossGaussianMovingSlot.positive_window_joint_slot_witness
  have h1 : Step1.Hyp (Gauss.sample d) 0 s t :=
    Gauss.step1Hyp_slot d (κ := 1) (by norm_num) 0 (by norm_num) s t
      base.hs0 base.hst base.ht1 c hc base.hreg base.hB
  have hJS : ∀ D : ℝ, 60 ≤ D →
      APrimeModel.JSNormDom (Gauss.sample d) 0 s t D :=
    jsNormDom_of_gaussian_hypotheses (κ := 1) (E := 0) (c := c)
      (s := s) (t := t) (by norm_num) (by norm_num)
      base.hs0 base.hst base.ht1 hc base.hreg base.hB
  have hStep2 := step2_of_gaussian_hypotheses
    (κ := 1) (E := 0) (c := c) (s := s) (t := t)
    (by norm_num) (by norm_num) (by norm_num)
    base.hs0 base.hst base.ht1 hc base.hreg base.hB
  exact ⟨c, hc, s, t, ⟨⟨base, h1, hJS, hStep2⟩⟩⟩

#print axioms jsNormDom_of_gaussian_hypotheses
#print axioms step2_of_gaussian_hypotheses
#print axioms positive_window_joint_step2_witness

end RBM.Gauss.APrimeFreeLossGaussianStep2
