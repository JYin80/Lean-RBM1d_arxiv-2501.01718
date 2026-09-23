/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Exact time mesh and finite net

The elementary time mesh and finite net used by the flow and Gaussian facades.
-/

namespace RBM

/-- **The mesh that matches the pair `(Kmod, γ)`**: `m_N = (N+1)^{Kmod/γ}`.  At `(1, 1/2)` this
is the `(N+1)²` of `RBM.Step2FarMart.mesh_fine_one_at_sq`. -/
noncomputable def meshK (Kmod γ : ℝ) : ℕ → ℝ := fun N => ((N : ℝ) + 1) ^ (Kmod / γ)

theorem meshK_pos (Kmod γ : ℝ) (N : ℕ) : 0 < meshK Kmod γ N :=
  Real.rpow_pos_of_pos (by positivity) _

namespace MomentDuhamelCut

/-- **The net `{s_N + k/m_N}` of (5.46) inside the window, as a `Finset`.**

`RBM.Step2MomentStep.netSet` is the same family as a `Set`; the union bound of
`hev_of_cutHyp` needs it to be finite, and its cardinality to be polynomial in `N`, so it is
recorded here as a `Finset`. -/
noncomputable def netFinset (s t m : ℕ → ℝ) (N : ℕ) : Finset ℝ :=
  Finset.image (fun k : ℕ => s N + (k : ℝ) / m N)
    (Finset.range (⌊(t N - s N) * m N⌋₊ + 1))

/-- **Every net point lies in the window.**  The index is cut at `⌊(t_N - s_N) m_N⌋`, not at
the ceiling, precisely so that this holds: the union bound of `hev_of_cutHyp` runs over the
whole `Finset`, and the moment hypothesis is only ever asserted inside the window. -/
theorem netFinset_subset_Icc {s t m : ℕ → ℝ} {N : ℕ} (hst : s N ≤ t N) (hm : 0 < m N) :
    ∀ ws ∈ netFinset s t m N, ws ∈ Set.Icc (s N) (t N) := by
  intro ws hws
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hws
  have hkle : k ≤ ⌊(t N - s N) * m N⌋₊ := by
    have := Finset.mem_range.1 hk; omega
  have hnn : (0 : ℝ) ≤ (t N - s N) * m N := by
    have : (0 : ℝ) ≤ t N - s N := by linarith
    positivity
  have h1 : (k : ℝ) ≤ (t N - s N) * m N :=
    le_trans (by exact_mod_cast Nat.cast_le.2 hkle) (Nat.floor_le hnn)
  have h2 : (k : ℝ) / m N ≤ t N - s N := by rw [div_le_iff₀ hm]; exact h1
  have h3 : (0 : ℝ) ≤ (k : ℝ) / m N := div_nonneg (Nat.cast_nonneg k) hm.le
  exact ⟨by linarith, by linarith⟩

end MomentDuhamelCut

end RBM
