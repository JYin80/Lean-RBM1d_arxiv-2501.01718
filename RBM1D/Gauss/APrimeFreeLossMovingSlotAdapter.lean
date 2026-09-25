/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeAssembly
import RBM1D.Gauss.APrimeGeneralMovingDetFields
import RBM1D.Gauss.APrimeGeneralMovingGoodMesh
import RBM1D.Gauss.APrimeGeneralMovingMesh
import RBM1D.Gauss.APrimeSlotFields
import RBM1D.Gauss.APrimeWeight

/-!
# T1321: conditional moving-window slot adapter

The moving-window deterministic package supplies the event-restricted fields
of `APrimeHypOn` for the actual Gaussian model.  The only remaining input here
is the literal post-summation family estimate at the order-dependent widened
weight.  This adapter does not prove that estimate.
-/

namespace RBM.APrimeFreeLossMovingSlotAdapter

open Filter MeasureTheory Step2Bootstrap CutHypTheta MomentDuhamelCut

open scoped Matrix.Norms.L2Operator

noncomputable section

/-- A conditional moving-window adapter from the literal widened-weight
family estimate to the actual `APrimeSlot'`.

Unlike the frozen-window assembler, the modulus and net fields are taken
directly from `DetFieldPackage`; no uniform upper endpoint `t₀ < 1` is
introduced.  The widened-weight family estimate is the sole unproved
analytical input.
-/
def slot_of_widened_family
    {E D c δ₀ : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg (Gauss.band Gauss.Dims.exampleGrow) E s t c)
    (hδ₀ : 0 < δ₀)
    (hfamily : ∀ δ, 0 < δ → δ ≤ δ₀ → ∀ p : ℕ,
      ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
        ∀ k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N,
          ∫ ω, APrimeWeight.widenedW
            (APrimeWeight.canonicalR s t (APrimeGeneralMovingMesh.targetMesh D)) 1
            (fun N u ω => Step2Moment.jSnorm
              (Gauss.sample Gauss.Dims.exampleGrow) E D s N u ω)
            s t (APrimeGeneralMovingMesh.targetMesh D) δ p N k ω *
            |cutTrunc ((N : ℝ) ^ (2 * δ))
              (Step2Moment.jSnorm (Gauss.sample Gauss.Dims.exampleGrow) E D s N
                (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k) ω)| ^ (2 * p)
            ∂(Gauss.band Gauss.Dims.exampleGrow).P
          ≤ C * (N : ℝ) ^ (δ / 2 * (p : ℝ))) :
    APrimeSlotFields.APrimeSlot' (Gauss.sample Gauss.Dims.exampleGrow) E s t D := by
  let d : Gauss.Dims := Gauss.Dims.exampleGrow
  let mesh : ℕ → ℝ := APrimeGeneralMovingMesh.targetMesh D
  let J : ℕ → ℝ → Gauss.Ω d → ℝ := fun N u ω =>
    Step2Moment.jSnorm (Gauss.sample d) E D s N u ω
  let W : ℝ → ℕ → ℕ → Gauss.Ω d → ℝ :=
    APrimeWeight.piecewiseW (APrimeWeight.canonicalR s t mesh) 1 J s t mesh
  let Wp : ℕ → ℝ → ℕ → ℕ → Gauss.Ω d → ℝ := fun p δ N k ω =>
    APrimeWeight.widenedW (APrimeWeight.canonicalR s t mesh) 1 J s t mesh δ p N k ω
  letI := (Gauss.band d).isProbabilityMeasure
  have hfields := APrimeWeight.jSnorm_piecewiseW_fields
    (P := (Gauss.band d).P) (Gauss.sample d) E D s t mesh
  have hWm : ∀ δ N k, AEStronglyMeasurable (W δ N k) (Gauss.band d).P := hfields.1
  have hW0 : ∀ δ N k ω, 0 ≤ W δ N k ω := hfields.2.1
  have hW1 : ∀ δ N k ω, W δ N k ω ≤ 1 := hfields.2.2.1
  have hWdom : ∀ δ N k ω,
      ω ∈ prefNet J s mesh (fun N _ => (N : ℝ) ^ (2 * δ) * 1) N k →
        1 ≤ W δ N k ω := hfields.2.2.2
  have hJ0 : ∀ N u ω, 0 ≤ J N u ω := by
    intro N u ω
    exact div_nonneg
      (zero_le_one.trans (Step2Moment.one_le_jS (Gauss.sample d) N u ω))
      (by positivity)
  have hJmeas : ∀ N u, Measurable (J N u) := fun N u =>
    APrimeSlotFields.measurable_jSnorm (Gauss.sample d) E D s N u
  have hWp0 : ∀ p δ N k ω, 0 ≤ Wp p δ N k ω := by
    intro p δ N k ω
    exact APrimeWeight.widenedW_nonneg _ _ _ _ _ _ _ _ _ _ ω
  have hWp1 : ∀ p δ N k ω, Wp p δ N k ω ≤ 1 := by
    intro p δ N k ω
    exact APrimeWeight.widenedW_le_one _ _ _ _ _ _ _ _ _ _ ω
  have hWpm : ∀ p δ N k, AEStronglyMeasurable (Wp p δ N k) (Gauss.band d).P := by
    intro p δ N k
    exact APrimeWeight.widenedW_meas _ _ _ _ _ _ hJmeas p δ N k
  have hWle : ∀ p δ N k ω, W δ N k ω ≤ Wp p δ N k ω := by
    intro p δ N k ω
    exact APrimeWeight.piecewiseW_le_widenedW (by norm_num) δ p N k ω
  have hmom : WeightedMoment (Gauss.band d).P J s t mesh
      (fun _ _ => (1 : ℝ)) (fun _ => 1) δ₀ W := by
    exact APrimeAssembly.weightedMoment_of_widened_family hJ0
      (fun N u => (hJmeas N u).aestronglyMeasurable)
      hW0 hW1 hWm hWp0 hWp1 hWpm hWle hfamily
  let H := APrimeGeneralMovingDetFields.detFieldPackage
    hE hD hs0 hst ht1 hc hreg
  have hHyp : APrimeHypOn (Gauss.band d).P J s t
      (fun _ _ => (1 : ℝ)) (fun _ => 1) APrimeGeneralMovingGoodMesh.good := by
    refine
      { window := H.window
        δ₀ := δ₀
        δ₀_pos := hδ₀
        Θ_pos := H.Theta_pos
        lev_ge := H.lev_ge
        J_nonneg := H.J_nonneg
        meas := H.meas
        good_meas := H.good_meas
        mesh := mesh
        mesh_pos := H.mesh_pos
        Kmod := APrimeGeneralMovingFieldPackage.Kmod D
        γ := APrimeGeneralMovingFieldPackage.gamma
        γ_pos := H.gamma_pos
        modulus := ?_
        mesh_fine := H.mesh_fine
        Ccard := APrimeGeneralMovingFieldPackage.Ccard D
        card_le := H.card_le
        Clev := APrimeGeneralMovingDetFields.Clev
        Clev_nonneg := H.Clev_nonneg
        levpoly := H.levpoly
        W := W
        W_meas := hWm
        W_nonneg := hW0
        W_le_one := hW1
        W_dom := hWdom
        weightedMoment := hmom }
    · simpa [APrimeGeneralMovingDetFields.J] using H.modulus
  exact ⟨APrimeGeneralMovingGoodMesh.good, hHyp, H.good_highProb⟩

/-- The source package already supplies a non-degenerate same-model window
and a nonempty high-probability good event at `E = 0`, `D = 60`.  This is a
witness for the deterministic and event assumptions of the adapter; it does
not assert its conditional family-moment premise. -/
theorem positive_length_model_window_witness :
    ∃ τ' : ℝ, 0 < τ' ∧ ∃ c : ℝ, 0 < c ∧ ∃ s t : ℕ → ℝ,
      (∀ N, 0 ≤ s N) ∧ (∀ N, s N ≤ t N) ∧ (∀ N, t N < 1) ∧
      Cond272Reg (Gauss.band Gauss.Dims.exampleGrow) 0 s t c ∧
      (∀ᶠ N : ℕ in atTop, s N < t N) ∧
      APrimeGeneralMovingDetFields.DetFieldPackage 0 60 s t ∧
      HighProb (Gauss.band Gauss.Dims.exampleGrow).P APrimeGeneralMovingGoodMesh.good ∧
      (∀ N, (APrimeGeneralMovingGoodMesh.good N).Nonempty) := by
  obtain ⟨τ', hτ', c, hc, s, t, hs0, hst, ht1, hreg, hpos, H⟩ :=
    APrimeGeneralMovingDetFields.positive_length_det_field_package_witness
  exact ⟨τ', hτ', c, hc, s, t, hs0, hst, ht1, hreg, hpos, H,
    H.good_highProb, H.good_nonempty⟩

#print axioms slot_of_widened_family
#print axioms positive_length_model_window_witness

end

end RBM.APrimeFreeLossMovingSlotAdapter
