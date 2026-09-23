/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingMesh
import RBM1D.Gauss.APrimeGeneralMovingWindowFloor

/-!
# T478: concrete norm event and mesh package on moving windows

The fixed event `{‖Xmat‖ ≤ N}` is bundled with T474's polynomial mesh
fields.  No modulus or moment assertion is part of this package.
-/

namespace RBM.APrimeGeneralMovingGoodMesh

open Filter MeasureTheory Set Gauss

open scoped Matrix.Norms.L2Operator

/-- The fixed norm event, independent of every window and bootstrap
parameter. -/
def good (N : ℕ) : Set (Ω Dims.exampleGrow) :=
  {ω : Ω Dims.exampleGrow |
    ‖Xmat Dims.exampleGrow N ω‖ ≤ (N : ℝ)}

theorem measurableSet_good (N : ℕ) : MeasurableSet (good N) := by
  simpa only [good] using
    (Gauss.measurableSet_normX_le Dims.exampleGrow N)

theorem highProb_good : HighProb (P Dims.exampleGrow) good := by
  change HighProb (P Dims.exampleGrow)
    (fun N => {ω : Ω Dims.exampleGrow |
      ‖Xmat Dims.exampleGrow N ω‖ ≤ (N : ℝ)})
  exact Gauss.highProb_norm_Xmat_le Dims.exampleGrow

theorem zero_mem_good (N : ℕ) : (0 : Ω Dims.exampleGrow) ∈ good N := by
  simpa only [good] using
    (APrimeSlotFields.zero_mem_normX_le Dims.exampleGrow N)

theorem good_nonempty (N : ℕ) : (good N).Nonempty :=
  ⟨0, zero_mem_good N⟩

/-- The concrete deterministic and probabilistic fields available before
the pending modulus and weighted-moment constructions. -/
structure GoodMeshPackage (D : ℝ) (s t : ℕ → ℝ) : Prop where
  good_measurable : ∀ N, MeasurableSet (good N)
  good_highProb : HighProb (P Dims.exampleGrow) good
  good_nonempty : ∀ N, (good N).Nonempty
  mesh_pos : ∀ N, 0 < APrimeGeneralMovingMesh.targetMesh D N
  mesh_fine : ∀ᶠ N : ℕ in atTop,
    (N : ℝ) ^ (2 * D + 7) *
        (1 / APrimeGeneralMovingMesh.targetMesh D N) ^ ((1 : ℝ) / 2) ≤ 1
  card_le : ∀ᶠ N : ℕ in atTop,
    (t N - s N) * APrimeGeneralMovingMesh.targetMesh D N + 2 ≤
      (N : ℝ) ^ (4 * D + 19)

/-- Concrete package for every deterministic moving window in `[0,1)`.
Its event and mesh do not depend on the particular endpoint sequence. -/
theorem goodMeshPackage {D : ℝ} {s t : ℕ → ℝ}
    (hD : 60 ≤ D) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) : GoodMeshPackage D s t := by
  have hmesh := APrimeGeneralMovingMesh.target_aprime_mesh_fields
    hD hs0 hst ht1
  exact
    { good_measurable := measurableSet_good
      good_highProb := highProb_good
      good_nonempty := good_nonempty
      mesh_pos := hmesh.1
      mesh_fine := hmesh.2.1
      card_le := hmesh.2.2 }

/-- The package exposes exactly the event and mesh fields that can be
inserted into a later `APrimeHypOn` constructor. -/
theorem good_mesh_fields {D : ℝ} {s t : ℕ → ℝ}
    (hD : 60 ≤ D) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) :
    (∀ N, MeasurableSet (good N)) ∧
    HighProb (P Dims.exampleGrow) good ∧
    (∀ N, (good N).Nonempty) ∧
    (∀ N, 0 < APrimeGeneralMovingMesh.targetMesh D N) ∧
    (∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (2 * D + 7) *
          (1 / APrimeGeneralMovingMesh.targetMesh D N) ^ ((1 : ℝ) / 2) ≤ 1) ∧
    (∀ᶠ N : ℕ in atTop,
      (t N - s N) * APrimeGeneralMovingMesh.targetMesh D N + 2 ≤
        (N : ℝ) ^ (4 * D + 19)) := by
  let H := goodMeshPackage hD hs0 hst ht1
  exact ⟨H.good_measurable, H.good_highProb, H.good_nonempty,
    H.mesh_pos, H.mesh_fine, H.card_le⟩

/-- T473's separate positive-length admissible grid witness.  This statement
does not identify its existential window with any independently chosen
sample. -/
theorem positive_length_admissible_grid_window :
    ∃ τ' : ℝ, 0 < τ' ∧ ∃ c : ℝ, 0 < c ∧ ∃ s t : ℕ → ℝ,
      (∀ N, 0 ≤ s N) ∧ (∀ N, s N ≤ t N) ∧ (∀ N, t N < 1) ∧
      Cond272Reg (band Dims.exampleGrow) 0 s t c ∧
        ∀ᶠ N : ℕ in atTop, s N < t N :=
  APrimeGeneralMovingWindowFloor.positive_length_grid_window_witness

#print axioms measurableSet_good
#print axioms highProb_good
#print axioms zero_mem_good
#print axioms good_nonempty
#print axioms goodMeshPackage
#print axioms good_mesh_fields
#print axioms positive_length_admissible_grid_window

end RBM.APrimeGeneralMovingGoodMesh
