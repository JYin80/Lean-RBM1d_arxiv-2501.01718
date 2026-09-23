/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingLoopModulus
import RBM1D.Gauss.APrimeGeneralMovingGoodMesh

/-!
# T479: concrete moving-window normalized-loop field package

This module combines T475's modulus with T478's identical norm event and
target mesh.  It packages only the event, modulus, and mesh/cardinality
fields for the actual `jSnorm` functional.
-/

namespace RBM.APrimeGeneralMovingFieldPackage

open Filter MeasureTheory Set Gauss

open scoped Matrix.Norms.L2Operator

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

/-- The exact modulus exponent supplied by T475. -/
noncomputable def Kmod (D : ℝ) : ℝ := 2 * D + 7

/-- The exact Hölder exponent supplied by T475. -/
noncomputable def gamma : ℝ := 1 / 2

/-- The exact mesh-cardinality exponent supplied by T478. -/
noncomputable def Ccard (D : ℝ) : ℝ := 4 * D + 19

/-- The concrete event/modulus/mesh fields for `jSnorm` on one admissible
moving window.  The displayed exponents are definitionally the fixed values
`Kmod = 2D+7`, `gamma = 1/2`, and `Ccard = 4D+19`. -/
structure JNormFieldPackage (E D : ℝ) (s t : ℕ → ℝ) : Prop where
  good_measurable : ∀ N,
    MeasurableSet (APrimeGeneralMovingGoodMesh.good N)
  good_highProb :
    HighProb (P d) APrimeGeneralMovingGoodMesh.good
  good_nonempty : ∀ N,
    (APrimeGeneralMovingGoodMesh.good N).Nonempty
  mesh_pos : ∀ N,
    0 < APrimeGeneralMovingMesh.targetMesh D N
  modulus : ∀ᶠ N : ℕ in atTop,
    ∀ ω ∈ APrimeGeneralMovingGoodMesh.good N,
      ∀ v ∈ Icc (s N) (t N), ∀ w ∈ Icc (s N) (t N),
        |Step2Moment.jSnorm (sample d) E D s N v ω -
            Step2Moment.jSnorm (sample d) E D s N w ω| ≤
          (N : ℝ) ^ Kmod D * |v - w| ^ gamma
  mesh_fine : ∀ᶠ N : ℕ in atTop,
    (N : ℝ) ^ Kmod D *
        (1 / APrimeGeneralMovingMesh.targetMesh D N) ^ gamma ≤ 1
  card_le : ∀ᶠ N : ℕ in atTop,
    (t N - s N) * APrimeGeneralMovingMesh.targetMesh D N + 2 ≤
      (N : ℝ) ^ Ccard D

/-- T475 and T478 assemble into one concrete package on the same event and
the same moving window. -/
theorem jNormFieldPackage {E D c : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c) :
    JNormFieldPackage E D s t := by
  have hmesh := APrimeGeneralMovingGoodMesh.goodMeshPackage
    hD hs0 hst ht1
  have hmod := APrimeGeneralMovingLoopModulus.eventually_jSnorm_modulus
    hE hD hs0 hst ht1 hc hreg
  exact
    { good_measurable := hmesh.good_measurable
      good_highProb := hmesh.good_highProb
      good_nonempty := hmesh.good_nonempty
      mesh_pos := hmesh.mesh_pos
      modulus := by
        simpa only [APrimeGeneralMovingGoodMesh.good, Kmod, gamma] using hmod
      mesh_fine := by
        simpa only [Kmod, gamma] using hmesh.mesh_fine
      card_le := by
        simpa only [Ccard] using hmesh.card_le }

/-- The bundled fields exposed as one conjunction with their exact public
shapes. -/
theorem concrete_fields {E D c : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c) :
    (∀ N, MeasurableSet (APrimeGeneralMovingGoodMesh.good N)) ∧
    HighProb (P d) APrimeGeneralMovingGoodMesh.good ∧
    (∀ N, (APrimeGeneralMovingGoodMesh.good N).Nonempty) ∧
    (∀ N, 0 < APrimeGeneralMovingMesh.targetMesh D N) ∧
    (∀ᶠ N : ℕ in atTop,
      ∀ ω ∈ APrimeGeneralMovingGoodMesh.good N,
        ∀ v ∈ Icc (s N) (t N), ∀ w ∈ Icc (s N) (t N),
          |Step2Moment.jSnorm (sample d) E D s N v ω -
              Step2Moment.jSnorm (sample d) E D s N w ω| ≤
            (N : ℝ) ^ (2 * D + 7) * |v - w| ^ ((1 : ℝ) / 2)) ∧
    (∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (2 * D + 7) *
          (1 / APrimeGeneralMovingMesh.targetMesh D N) ^ ((1 : ℝ) / 2) ≤ 1) ∧
    (∀ᶠ N : ℕ in atTop,
      (t N - s N) * APrimeGeneralMovingMesh.targetMesh D N + 2 ≤
        (N : ℝ) ^ (4 * D + 19)) := by
  let H := jNormFieldPackage hE hD hs0 hst ht1 hc hreg
  exact ⟨H.good_measurable, H.good_highProb, H.good_nonempty, H.mesh_pos,
    by simpa only [Kmod, gamma] using H.modulus,
    by simpa only [Kmod, gamma] using H.mesh_fine,
    by simpa only [Ccard] using H.card_le⟩

/-- Nondegenerate satisfiability witness: T473's positive-length admissible
grid window carries the complete concrete package at `E = 0`, `D = 60`.
Its fixed norm event is nonempty for every `N`. -/
theorem positive_length_field_package_witness :
    ∃ τ' : ℝ, 0 < τ' ∧ ∃ c : ℝ, 0 < c ∧ ∃ s t : ℕ → ℝ,
      (∀ N, 0 ≤ s N) ∧ (∀ N, s N ≤ t N) ∧ (∀ N, t N < 1) ∧
      Cond272Reg B 0 s t c ∧ (∀ᶠ N : ℕ in atTop, s N < t N) ∧
      JNormFieldPackage 0 60 s t := by
  obtain ⟨τ', hτ', c, hc, s, t, hs0, hst, ht1, hreg, hpos⟩ :=
    APrimeGeneralMovingWindowFloor.positive_length_grid_window_witness
  exact ⟨τ', hτ', c, hc, s, t, hs0, hst, ht1, hreg, hpos,
    jNormFieldPackage (by norm_num) (by norm_num) hs0 hst ht1 hc hreg⟩

#print axioms jNormFieldPackage
#print axioms concrete_fields
#print axioms positive_length_field_package_witness

end
end RBM.APrimeGeneralMovingFieldPackage
