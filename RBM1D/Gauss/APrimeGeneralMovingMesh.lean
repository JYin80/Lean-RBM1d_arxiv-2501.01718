/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Step2Bootstrap

/-!
# T474: polynomial meshes on general moving windows

This file supplies the deterministic `mesh_pos`, `mesh_fine`, and `card_le`
arithmetic needed by `Step2Bootstrap.APrimeHypOn` on arbitrary moving windows
inside `[0,1)`.
-/

namespace RBM.APrimeGeneralMovingMesh

open Filter

/-- A mesh which is positive even at `N = 0` and agrees eventually with
`N^(2K+4)`. -/
noncomputable def polynomialMesh (K : ℝ) (N : ℕ) : ℝ :=
  if N = 0 then 1 else (N : ℝ) ^ (2 * K + 4)

@[simp] theorem polynomialMesh_zero (K : ℝ) : polynomialMesh K 0 = 1 := by
  simp [polynomialMesh]

theorem polynomialMesh_eq_of_pos {K : ℝ} {N : ℕ} (hN : 0 < N) :
    polynomialMesh K N = (N : ℝ) ^ (2 * K + 4) := by
  simp [polynomialMesh, hN.ne']

theorem polynomialMesh_pos (K : ℝ) (N : ℕ) : 0 < polynomialMesh K N := by
  by_cases hN : N = 0
  · subst N
    simp
  · rw [polynomialMesh, ite_eq_right hN]
    exact Real.rpow_pos_of_pos (by exact_mod_cast (Nat.pos_of_ne_zero hN)) _

theorem eventually_polynomialMesh_eq (K : ℝ) :
    ∀ᶠ N : ℕ in atTop,
      polynomialMesh K N = (N : ℝ) ^ (2 * K + 4) := by
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact polynomialMesh_eq_of_pos (by omega)

/-- Exact square-root mesh arithmetic for positive `N`. -/
theorem mesh_fine_eq_inv_sq {K : ℝ} {N : ℕ} (hN : 1 ≤ N) :
    (N : ℝ) ^ K * (1 / polynomialMesh K N) ^ ((1 : ℝ) / 2) =
      (N : ℝ) ^ (-(2 : ℝ)) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  rw [polynomialMesh_eq_of_pos (show 0 < N by omega)]
  have hinv : 1 / (N : ℝ) ^ (2 * K + 4) =
      (N : ℝ) ^ (-(2 * K + 4)) := by
    rw [Real.rpow_neg hNR.le, one_div]
  rw [hinv, ← Real.rpow_mul hNR.le, ← Real.rpow_add hNR]
  congr 1
  ring

theorem inv_sq_le_one {N : ℕ} (hN : 1 ≤ N) :
    (N : ℝ) ^ (-(2 : ℝ)) ≤ 1 := by
  exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hN) (by norm_num)

/-- Stronger than the `APrimeHypOn.mesh_fine` field at `γ=1/2` and
`Θ=1`: the left side equals `N^-2`. -/
theorem eventually_mesh_fine (K : ℝ) :
    ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ K * (1 / polynomialMesh K N) ^ ((1 : ℝ) / 2) ≤
        (N : ℝ) ^ (-(2 : ℝ)) ∧
      (N : ℝ) ^ (-(2 : ℝ)) ≤ 1 := by
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact ⟨(mesh_fine_eq_inv_sq hN).le, inv_sq_le_one hN⟩

/-- Exact `Step2Bootstrap.APrimeHypOn.mesh_fine` shape with `Θ ≡ 1`. -/
theorem eventually_aprime_mesh_fine (K : ℝ) :
    ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ K * (1 / polynomialMesh K N) ^ ((1 : ℝ) / 2) ≤ 1 := by
  filter_upwards [eventually_mesh_fine K] with N hN
  exact hN.1.trans hN.2

/-- Polynomial cardinality budget on every deterministic moving window in
`[0,1)`.  The result has the exact `APrimeHypOn.card_le` shape. -/
theorem eventually_card_le {s t : ℕ → ℝ} (K : ℝ) (hK : 0 ≤ K)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) :
    ∀ᶠ N : ℕ in atTop,
      (t N - s N) * polynomialMesh K N + 2 ≤
        (N : ℝ) ^ (2 * K + 5) := by
  filter_upwards [eventually_ge_atTop 3] with N hN
  have hNpos : 0 < N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hNR3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hdiff0 : 0 ≤ t N - s N := sub_nonneg.mpr (hst N)
  have hdiff1 : t N - s N ≤ 1 := by linarith [hs0 N, ht1 N]
  have hexp : 0 ≤ 2 * K + 4 := by linarith
  have hmesh1 : 1 ≤ (N : ℝ) ^ (2 * K + 4) :=
    Real.one_le_rpow (by linarith) hexp
  rw [polynomialMesh_eq_of_pos hNpos]
  have hleft :
      (t N - s N) * (N : ℝ) ^ (2 * K + 4) + 2 ≤
        (N : ℝ) ^ (2 * K + 4) + 2 := by
    simpa only [one_mul, add_comm] using add_le_add_right
      (mul_le_mul_of_nonneg_right hdiff1
        (Real.rpow_nonneg hNR.le (2 * K + 4))) 2
  have hmiddle :
      (N : ℝ) ^ (2 * K + 4) + 2 ≤
        (N : ℝ) * (N : ℝ) ^ (2 * K + 4) := by
    nlinarith
  calc
    (t N - s N) * (N : ℝ) ^ (2 * K + 4) + 2 ≤
        (N : ℝ) ^ (2 * K + 4) + 2 := hleft
    _ ≤ (N : ℝ) * (N : ℝ) ^ (2 * K + 4) := hmiddle
    _ = (N : ℝ) ^ (2 * K + 5) := by
      calc
        (N : ℝ) * (N : ℝ) ^ (2 * K + 4) =
            (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (2 * K + 4) := by
          rw [Real.rpow_one]
        _ = (N : ℝ) ^ ((1 : ℝ) + (2 * K + 4)) :=
          (Real.rpow_add hNR 1 (2 * K + 4)).symm
        _ = (N : ℝ) ^ (2 * K + 5) := by ring_nf

/-- The three deterministic fields can be inserted directly into an
`APrimeHypOn` constructor. -/
theorem aprime_mesh_fields {s t : ℕ → ℝ} (K : ℝ) (hK : 0 ≤ K)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) :
    (∀ N, 0 < polynomialMesh K N) ∧
    (∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ K * (1 / polynomialMesh K N) ^ ((1 : ℝ) / 2) ≤ 1) ∧
    (∀ᶠ N : ℕ in atTop,
      (t N - s N) * polynomialMesh K N + 2 ≤
        (N : ℝ) ^ (2 * K + 5)) :=
  ⟨polynomialMesh_pos K, eventually_aprime_mesh_fine K,
    eventually_card_le K hK hs0 hst ht1⟩

/-! ## The `K = 2D+7` instance -/

/-- The mesh used at the target general-window modulus exponent. -/
noncomputable def targetMesh (D : ℝ) (N : ℕ) : ℝ :=
  polynomialMesh (2 * D + 7) N

theorem targetMesh_pos (D : ℝ) (N : ℕ) : 0 < targetMesh D N :=
  polynomialMesh_pos (2 * D + 7) N

theorem eventually_targetMesh_eq (D : ℝ) :
    ∀ᶠ N : ℕ in atTop,
      targetMesh D N = (N : ℝ) ^ (4 * D + 18) := by
  filter_upwards [eventually_polynomialMesh_eq (2 * D + 7)] with N hN
  unfold targetMesh
  rw [hN]
  congr 1
  ring

theorem eventually_target_mesh_fine (D : ℝ) :
    ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (2 * D + 7) *
          (1 / targetMesh D N) ^ ((1 : ℝ) / 2) ≤
        (N : ℝ) ^ (-(2 : ℝ)) ∧
      (N : ℝ) ^ (-(2 : ℝ)) ≤ 1 := by
  simpa only [targetMesh] using eventually_mesh_fine (2 * D + 7)

theorem eventually_target_aprime_mesh_fine (D : ℝ) :
    ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (2 * D + 7) *
          (1 / targetMesh D N) ^ ((1 : ℝ) / 2) ≤ 1 := by
  simpa only [targetMesh] using eventually_aprime_mesh_fine (2 * D + 7)

theorem eventually_target_card_le {s t : ℕ → ℝ} {D : ℝ}
    (hD : 60 ≤ D) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) :
    ∀ᶠ N : ℕ in atTop,
      (t N - s N) * targetMesh D N + 2 ≤
        (N : ℝ) ^ (4 * D + 19) := by
  have hK : 0 ≤ 2 * D + 7 := by linarith
  filter_upwards [eventually_card_le (2 * D + 7) hK hs0 hst ht1]
      with N hN
  unfold targetMesh
  have hexp : 2 * (2 * D + 7) + 5 = 4 * D + 19 := by ring
  rw [hexp] at hN
  exact hN

/-- Exact target adapter for the three `APrimeHypOn` mesh fields. -/
theorem target_aprime_mesh_fields {s t : ℕ → ℝ} {D : ℝ}
    (hD : 60 ≤ D) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) :
    (∀ N, 0 < targetMesh D N) ∧
    (∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (2 * D + 7) *
          (1 / targetMesh D N) ^ ((1 : ℝ) / 2) ≤ 1) ∧
    (∀ᶠ N : ℕ in atTop,
      (t N - s N) * targetMesh D N + 2 ≤
        (N : ℝ) ^ (4 * D + 19)) :=
  ⟨targetMesh_pos D, eventually_target_aprime_mesh_fine D,
    eventually_target_card_le hD hs0 hst ht1⟩

/-! ## Nondegenerate sample window -/

noncomputable def sampleStart (_N : ℕ) : ℝ := 0

noncomputable def sampleEnd (_N : ℕ) : ℝ := 1 / 2

theorem sample_window_geometry (N : ℕ) :
    0 ≤ sampleStart N ∧ sampleStart N < sampleEnd N ∧
      sampleEnd N < 1 := by
  norm_num [sampleStart, sampleEnd]

/-- A positive-length moving-window witness carrying all target mesh
arithmetic, with no stochastic assumptions. -/
theorem sample_target_mesh_fields {D : ℝ} (hD : 60 ≤ D) :
    (∀ N, 0 ≤ sampleStart N) ∧
    (∀ N, sampleStart N ≤ sampleEnd N) ∧
    (∀ N, sampleEnd N < 1) ∧
    (∀ N, sampleStart N < sampleEnd N) ∧
    (∀ N, 0 < targetMesh D N) ∧
    (∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (2 * D + 7) *
          (1 / targetMesh D N) ^ ((1 : ℝ) / 2) ≤ 1) ∧
    (∀ᶠ N : ℕ in atTop,
      (sampleEnd N - sampleStart N) * targetMesh D N + 2 ≤
        (N : ℝ) ^ (4 * D + 19)) := by
  have hgeom : ∀ N,
      0 ≤ sampleStart N ∧ sampleStart N < sampleEnd N ∧
        sampleEnd N < 1 := sample_window_geometry
  have hfields := target_aprime_mesh_fields hD
    (fun N => (hgeom N).1) (fun N => (hgeom N).2.1.le)
    (fun N => (hgeom N).2.2)
  exact ⟨fun N => (hgeom N).1, fun N => (hgeom N).2.1.le,
    fun N => (hgeom N).2.2, fun N => (hgeom N).2.1,
    hfields.1, hfields.2.1, hfields.2.2⟩

#print axioms polynomialMesh_pos
#print axioms eventually_polynomialMesh_eq
#print axioms mesh_fine_eq_inv_sq
#print axioms eventually_mesh_fine
#print axioms eventually_card_le
#print axioms aprime_mesh_fields
#print axioms eventually_targetMesh_eq
#print axioms eventually_target_mesh_fine
#print axioms eventually_target_card_le
#print axioms target_aprime_mesh_fields
#print axioms sample_target_mesh_fields

end RBM.APrimeGeneralMovingMesh
