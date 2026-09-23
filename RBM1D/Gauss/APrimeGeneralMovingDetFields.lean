/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingFieldPackage
import RBM1D.Gauss.APrimeSlotFields

/-!
# T483: deterministic `APrimeHypOn` fields on general moving windows

T479 supplies the moving modulus, concrete norm event, and target mesh.
The remaining deterministic fields for the actual normalized loop follow
from the existing `APrimeSlotFields` proofs.  No weight or weighted moment
is introduced here.
-/

namespace RBM.APrimeGeneralMovingDetFields

open Filter MeasureTheory Set Gauss Step2Bootstrap MomentDuhamelCut

open scoped Matrix.Norms.L2Operator

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

/-- The actual normalized-loop state functional. -/
noncomputable abbrev J (E D : ℝ) (s : ℕ → ℝ) : ℕ → ℝ → Ω d → ℝ :=
  fun N u ω => Step2Moment.jSnorm (sample d) E D s N u ω

/-- The constant truncation level. -/
noncomputable def lev (_N : ℕ) (_u : ℝ) : ℝ := 1

/-- The constant control scale. -/
noncomputable def Theta (_N : ℕ) : ℝ := 1

/-- The exact truncation-level exponent. -/
noncomputable def Clev : ℝ := 1

/-- Nonnegativity of the actual normalized-loop state. -/
theorem J_nonneg (E D : ℝ) (s : ℕ → ℝ) (N : ℕ) (u : ℝ) (ω : Ω d) :
    0 ≤ J E D s N u ω := by
  have hJ : (0 : ℝ) ≤ Step2.jS (sample d) E D N u ω :=
    zero_le_one.trans (Step2Moment.one_le_jS (sample d) N u ω)
  have hR : (0 : ℝ) ≤ Step2Moment.ratR E s N u ^ 4 := by positivity
  exact div_nonneg hJ hR

/-- The `levpoly` field at `lev = Theta = Clev = 1`. -/
theorem eventually_levpoly {s t : ℕ → ℝ} {D : ℝ} :
    ∀ᶠ N : ℕ in atTop,
      ∀ ws ∈ netFinset s t (APrimeGeneralMovingMesh.targetMesh D) N,
        2 * lev N ws ≤ (N : ℝ) ^ Clev * Theta N := by
  simpa only [lev, Theta, Clev] using
    (APrimeSlotFields.eventually_levpoly_one
      (s := s) (t := t) (mesh := APrimeGeneralMovingMesh.targetMesh D))

/-- Every deterministic `APrimeHypOn`-shaped field for the concrete moving
window, event, mesh, and normalized-loop state. -/
structure DetFieldPackage (E D : ℝ) (s t : ℕ → ℝ) : Prop where
  window : ∀ N, s N ≤ t N
  Theta_pos : ∀ N, 0 < Theta N
  lev_ge : ∀ N, ∀ u ∈ Icc (s N) (t N), Theta N ≤ lev N u
  J_nonneg : ∀ N u ω, 0 ≤ J E D s N u ω
  meas : ∀ N u, Measurable fun ω => J E D s N u ω
  good_meas : ∀ N,
    MeasurableSet (APrimeGeneralMovingGoodMesh.good N)
  good_highProb :
    HighProb (P d) APrimeGeneralMovingGoodMesh.good
  good_nonempty : ∀ N,
    (APrimeGeneralMovingGoodMesh.good N).Nonempty
  mesh_pos : ∀ N,
    0 < APrimeGeneralMovingMesh.targetMesh D N
  gamma_pos : 0 < APrimeGeneralMovingFieldPackage.gamma
  modulus : ∀ᶠ N : ℕ in atTop,
    ∀ ω ∈ APrimeGeneralMovingGoodMesh.good N,
      ∀ v ∈ Icc (s N) (t N), ∀ w ∈ Icc (s N) (t N),
        |J E D s N v ω - J E D s N w ω| ≤
          (N : ℝ) ^ APrimeGeneralMovingFieldPackage.Kmod D *
            |v - w| ^ APrimeGeneralMovingFieldPackage.gamma
  mesh_fine : ∀ᶠ N : ℕ in atTop,
    (N : ℝ) ^ APrimeGeneralMovingFieldPackage.Kmod D *
        (1 / APrimeGeneralMovingMesh.targetMesh D N) ^
          APrimeGeneralMovingFieldPackage.gamma ≤ Theta N
  card_le : ∀ᶠ N : ℕ in atTop,
    (t N - s N) * APrimeGeneralMovingMesh.targetMesh D N + 2 ≤
      (N : ℝ) ^ APrimeGeneralMovingFieldPackage.Ccard D
  Clev_nonneg : 0 ≤ Clev
  levpoly : ∀ᶠ N : ℕ in atTop,
    ∀ ws ∈ netFinset s t (APrimeGeneralMovingMesh.targetMesh D) N,
      2 * lev N ws ≤ (N : ℝ) ^ Clev * Theta N

/-- Extend T479's concrete package by the remaining deterministic fields.
This theorem requires no `Cond272Reg`, since that hypothesis has already
been consumed in the supplied T479 package. -/
theorem detFieldPackage_of_base {E D : ℝ} {s t : ℕ → ℝ}
    (hwindow : ∀ N, s N ≤ t N)
    (H : APrimeGeneralMovingFieldPackage.JNormFieldPackage E D s t) :
    DetFieldPackage E D s t :=
  { window := hwindow
    Theta_pos := fun _ => one_pos
    lev_ge := fun _ _ _ => le_rfl
    J_nonneg := J_nonneg E D s
    meas := fun N u => APrimeSlotFields.measurable_jSnorm
      (sample d) E D s N u
    good_meas := H.good_measurable
    good_highProb := H.good_highProb
    good_nonempty := H.good_nonempty
    mesh_pos := H.mesh_pos
    gamma_pos := by norm_num [APrimeGeneralMovingFieldPackage.gamma]
    modulus := H.modulus
    mesh_fine := by simpa only [Theta] using H.mesh_fine
    card_le := H.card_le
    Clev_nonneg := by norm_num [Clev]
    levpoly := eventually_levpoly }

/-- Concrete deterministic field package under the original moving-window
assumptions. -/
theorem detFieldPackage {E D c : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c) :
    DetFieldPackage E D s t :=
  detFieldPackage_of_base hst
    (APrimeGeneralMovingFieldPackage.jNormFieldPackage
      hE hD hs0 hst ht1 hc hreg)

/-- The exact constants in the deterministic package. -/
theorem exact_parameters (D : ℝ) :
    APrimeGeneralMovingFieldPackage.Kmod D = 2 * D + 7 ∧
    APrimeGeneralMovingFieldPackage.gamma = (1 : ℝ) / 2 ∧
    APrimeGeneralMovingFieldPackage.Ccard D = 4 * D + 19 ∧
    Clev = 1 := by
  simp [APrimeGeneralMovingFieldPackage.Kmod,
    APrimeGeneralMovingFieldPackage.gamma,
    APrimeGeneralMovingFieldPackage.Ccard, Clev]

/-- Nondegenerate satisfiability witness obtained by extending T479's
positive-length package at `E=0`, `D=60`. -/
theorem positive_length_det_field_package_witness :
    ∃ τ' : ℝ, 0 < τ' ∧ ∃ c : ℝ, 0 < c ∧ ∃ s t : ℕ → ℝ,
      (∀ N, 0 ≤ s N) ∧ (∀ N, s N ≤ t N) ∧ (∀ N, t N < 1) ∧
      Cond272Reg B 0 s t c ∧ (∀ᶠ N : ℕ in atTop, s N < t N) ∧
      DetFieldPackage 0 60 s t := by
  obtain ⟨τ', hτ', c, hc, s, t, hs0, hst, ht1, hreg, hpos, H⟩ :=
    APrimeGeneralMovingFieldPackage.positive_length_field_package_witness
  exact ⟨τ', hτ', c, hc, s, t, hs0, hst, ht1, hreg, hpos,
    detFieldPackage_of_base hst H⟩

#print axioms J_nonneg
#print axioms eventually_levpoly
#print axioms detFieldPackage_of_base
#print axioms detFieldPackage
#print axioms exact_parameters
#print axioms positive_length_det_field_package_witness

end
end RBM.APrimeGeneralMovingDetFields
