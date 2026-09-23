/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingWindowFloor
import RBM1D.Gauss.Eq45FlowInputs

/-!
# T510: numerical inputs for the moving-window time net

This module supplies only the deterministic numerical fields of
`Gauss.stochDom_timeIcc_of_unifDom`, with block index `ZMod (L N)`,
`Cv = 1`, `K = 6`, `B = 1`, `γ = 1/2`, and `T = 1`.
The mesh spacing is exactly `N^(-16)`.
-/

namespace RBM.APrimeGeneralMovingNetNumerics

open Filter Set Gauss

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

/-- The spacing used for the general moving centered one-loop time net. -/
def meshSpacing (N : ℕ) : ℝ := (N : ℝ) ^ (-16 : ℝ)

/-- The exponent in the exact consumer is sixteen. -/
theorem net_exponent_eq : ((6 : ℝ) + 1 + 1) / (1 / 2) = 16 := by
  norm_num

theorem meshSpacing_nonneg (N : ℕ) : 0 ≤ meshSpacing N :=
  Real.rpow_nonneg (Nat.cast_nonneg N) _

theorem meshSpacing_pos {N : ℕ} (hN : 1 ≤ N) : 0 < meshSpacing N := by
  exact Real.rpow_pos_of_pos
    (by exact_mod_cast (show 0 < N by omega)) _

theorem eventually_meshSpacing_pos : ∀ᶠ N : ℕ in atTop, 0 < meshSpacing N := by
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  exact meshSpacing_pos hN

/-- The numerical spacing requirement holds at equality for positive N. -/
theorem net_spacing_eq {N : ℕ} (hN : 1 ≤ N) :
    (1 : ℝ) / (N : ℝ) ^ (((6 : ℝ) + 1 + 1) / (1 / 2)) = meshSpacing N := by
  have hN0 : (0 : ℝ) ≤ N := by exact_mod_cast (show 0 ≤ N by omega)
  rw [net_exponent_eq, meshSpacing, Real.rpow_neg hN0, one_div]

/-- The exact `hδ` field, with no loss in its exponent or constant. -/
theorem eventually_net_spacing_le :
    ∀ᶠ N : ℕ in atTop,
      (1 : ℝ) / (N : ℝ) ^ (((6 : ℝ) + 1 + 1) / (1 / 2)) ≤ meshSpacing N := by
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  exact (net_spacing_eq hN).le

/-- The original moving window has length between zero and one. -/
theorem window_length_bounds {s t : ℕ → ℝ}
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (N : ℕ) :
    0 ≤ t N - s N ∧ t N - s N ≤ 1 := by
  constructor
  · exact sub_nonneg.mpr (hst N)
  · linarith [hs0 N, ht1 N]

/-- The exact `hcard` field uses only the model's public block count. -/
theorem eventually_block_card_le :
    ∀ᶠ N : ℕ in atTop,
      (Fintype.card (ZMod (d.L N)) : ℝ) ≤ (N : ℝ) ^ (1 : ℝ) :=
  Gauss.card_ZMod_L_le d

/-- Numerical fields for the exact consumer. The control, event, fixed-time
law and time modulus are separate inputs and are not fields of this package. -/
structure NetNumerics (s t : ℕ → ℝ) : Prop where
  hcard : ∀ᶠ N : ℕ in atTop,
    (Fintype.card (ZMod (d.L N)) : ℝ) ≤ (N : ℝ) ^ (1 : ℝ)
  hst : ∀ N, s N ≤ t N
  hT : (0 : ℝ) < 1
  hlen : ∀ N, t N - s N ≤ 1
  hK : (0 : ℝ) ≤ 6
  hB : (0 : ℝ) ≤ 1
  hγ : (0 : ℝ) < 1 / 2
  hδ : ∀ᶠ N : ℕ in atTop,
    (1 : ℝ) / (N : ℝ) ^ (((6 : ℝ) + 1 + 1) / (1 / 2)) ≤ meshSpacing N

/-- Every original deterministic moving window supplies the numerical
package. No regularity or random estimate is required. -/
theorem netNumerics {s t : ℕ → ℝ}
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) : NetNumerics s t :=
  { hcard := eventually_block_card_le
    hst := hst
    hT := by norm_num
    hlen := fun N => (window_length_bounds hs0 hst ht1 N).2
    hK := by norm_num
    hB := by norm_num
    hγ := by norm_num
    hδ := eventually_net_spacing_le }

/-- The same T473 grid window has positive length and all numerical fields
simultaneously; the mesh is positive after the same eventual restriction. -/
theorem positive_length_grid_window_witness :
    ∃ τ' : ℝ, 0 < τ' ∧ ∃ c : ℝ, 0 < c ∧ ∃ s t : ℕ → ℝ,
      (∀ N, 0 ≤ s N) ∧ (∀ N, s N ≤ t N) ∧ (∀ N, t N < 1) ∧
      Cond272Reg B 0 s t c ∧ NetNumerics s t ∧
      ∀ᶠ N : ℕ in atTop, s N < t N ∧ 0 < meshSpacing N := by
  obtain ⟨τ', hτ', c, hc, s, t, hs0, hst, ht1, hreg, hlength⟩ :=
    APrimeGeneralMovingWindowFloor.positive_length_grid_window_witness
  refine ⟨τ', hτ', c, hc, s, t, hs0, hst, ht1, hreg,
    netNumerics hs0 hst ht1, ?_⟩
  filter_upwards [hlength, eventually_meshSpacing_pos] with N hlengthN hmesh
  exact ⟨hlengthN, hmesh⟩

#print axioms net_exponent_eq
#print axioms meshSpacing_nonneg
#print axioms meshSpacing_pos
#print axioms eventually_meshSpacing_pos
#print axioms net_spacing_eq
#print axioms eventually_net_spacing_le
#print axioms window_length_bounds
#print axioms eventually_block_card_le
#print axioms netNumerics
#print axioms positive_length_grid_window_witness

end
end RBM.APrimeGeneralMovingNetNumerics
